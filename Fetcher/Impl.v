Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fetcher.Ifc.

Section Impl.
  Context {ifcParams: Params}.
      
  Local Definition ShortVAddr := Bit (vAddrSz - 2).

  (* Instruction requests are always made at InstSz granularity *)
  Local Definition TopEntry: Kind
    := STRUCT_TYPE {
         "vaddr"  :: ShortVAddr; (* If lower is valid, then actual vaddr = shortVAddr >> 2; otherwise if only upper is valid, vaddr = (shortVaddr >> 2) + 2*)
         "immRes" :: immResK; (* Immediate response from memory *)
         "error"  :: finalErrK; (* Final error response from memory *)
         "upper"  :: Maybe CompInst; (* If lower is invalid, this contains either a full compressed inst or just the LSB portion of the next incomplete inst.
                                        If lower is valid, then it contains the MSB portion of an uncompressed inst *)
         "lower"  :: Maybe CompInst (* Always contains the LSB portion of an inst - either compressed or normal *)
       }.

  Local Instance fifoParams
    :  Fifo.Ifc.Params
    := {|
         Fifo.Ifc.name := (name ++ ".fifo")%string;
         Fifo.Ifc.k    := InRes;
         Fifo.Ifc.size := size
       |}.

  Context (fifo: @Fifo.Ifc.Ifc fifoParams).

  (* The register that assembles as full Inst from two CompInsts *)
  Local Definition topRegName := (Fetcher.Ifc.name ++ ".topReg")%string.

  (* Number of requests sent to memory *)
  Local Definition outstandingName := (Fetcher.Ifc.name ++ ".outstanding")%string.
  
  (* Number of responses from memory that have to be cleared *)
  Local Definition clearOutstandingName := (Fetcher.Ifc.name ++ ".clearOutstanding")%string.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition toVAddr ty (a: ShortVAddr @# ty) := ZeroExtendTruncMsb vAddrSz ({< a, $$(natToWord 2 0) >}).
  
  Local Definition isFull ty: ActionT ty Bool :=
    Read outstanding: Bit (lgSize + 1) <- outstandingName;
    LETA numFree <- Fifo.Ifc.numFree fifo;
    Ret (#numFree <= #outstanding).

  (* Only if true can the outstanding requests be cleared *)
  Local Definition canClear ty: ActionT ty Bool :=
    Read clearOutstanding: Bit (lgSize + 1) <- clearOutstandingName;
    Ret (#clearOutstanding == $0).

  Local Definition clear ty: ActionT ty Void :=
    LETA _ <- Fifo.Ifc.flush fifo;
    Read outstanding: Bit (lgSize + 1) <- outstandingName;
    Write clearOutstandingName: Bit (lgSize + 1) <- #outstanding;
    Write topRegName: TopEntry <- $$(getDefaultConst TopEntry);
    Retv.

  Local Definition isNextAddr ty (topAddr: ShortVAddr @# ty) (ftopAddr: VAddr @# ty) :=
    (topAddr + $1) == (ZeroExtendTruncMsb (vAddrSz - 2) ftopAddr).
  
  Local Definition isNotComplete
    ty
    (top : TopEntry @# ty)
    (ftop : Maybe InRes @# ty)
    : ActionT ty Bool :=
    Ret (! (isImmErr (top @% "immRes") || isFinalErr (top @% "error"))
         && (top @% "upper" @% "valid")
         && !(top @% "lower" @% "valid")
         && !(isCompressed (top @% "upper" @% "data"))
         && !((ftop @%"valid") && isNextAddr (top @% "vaddr") (ftop @% "data" @% "vaddr"))).

  (* If ftop doesn't complete the current upper in top, then drop ftop *)
  Local Definition notCompleteDeqRule ty: ActionT ty Void :=
    Read top: TopEntry <- topRegName;
    LETA ftop: Maybe InRes <- @Fifo.Ifc.first _ fifo _;
    LETA notComplete <- isNotComplete #top #ftop;
    If #notComplete && #ftop @% "valid" && !(isNextAddr (#top @% "vaddr") (#ftop @% "data" @% "vaddr"))
    then @Fifo.Ifc.deq _ fifo _;
    Retv.

  Local Definition isAligned ty (vaddr: VAddr @# ty) := ZeroExtendTruncLsb 2 vaddr == $0.

  Local Definition transferRule ty: ActionT ty Void :=
    LETA isEmp: Bool <- @Fifo.Ifc.isEmpty _ fifo _;
    Read top: TopEntry <- topRegName;
    If !(#top @% "upper" @% "valid") && !#isEmp
    then (
      LETA deqValM: Maybe InRes <- @Fifo.Ifc.deq _ fifo _;
      LET deqVal: InRes <- #deqValM @% "data";    
      LET lower <- STRUCT { "valid" ::= isAligned (#deqVal @% "vaddr") ;
                            "data"  ::= UniBit (TruncLsb _ _) (#deqVal @% "inst") };
      LET topEntry
        :  TopEntry
        <- STRUCT {
             "vaddr"  ::= ZeroExtendTruncMsb (vAddrSz - 2) (#deqVal @% "vaddr");
             "immRes" ::= #deqVal @% "immRes";
             "error"  ::= #deqVal @% "error";
             "upper"  ::= Valid (UniBit (TruncMsb _ _) (#deqVal @% "inst"));
             "lower"  ::= #lower};
      Write topRegName: TopEntry <- #topEntry;
      Retv );
    Retv.

  (* Invoked once memory sends back response *)
  Local Definition callback ty (res: ty InRes): ActionT ty Void :=
    Read clearOutstanding: Bit (lgSize + 1) <- clearOutstandingName;
    If #clearOutstanding == $0
    then (LETA _ <- @Fifo.Ifc.enq _ fifo _ res; Retv)
    else (Write clearOutstandingName : Bit (lgSize + 1) <- #clearOutstanding - $1; Retv);
    Read outstanding: Bit ((Nat.log2_up size) + 1) <- outstandingName;
    Write outstandingName <- #outstanding - $1;
    Retv.

  (* Invoked to send request to memory. The Bool returned by sendReq denotes whether the request was accepted *)
  Local Definition sendAddr (sendReq : forall ty, ty OutReq -> ActionT ty Bool) ty (req: ty OutReq) :=
    LETA retval <- sendReq _ req;
    Read outstanding: Bit ((Nat.log2_up size) + 1) <- outstandingName;
    Write outstandingName <- #outstanding + IF #retval then $1 else $0;
    Ret #retval.

  Local Definition isStraddle ty (top: TopEntry @# ty) :=
    !(top @% "lower" @% "valid") && !isCompressed (top @% "upper" @% "data").

  Local Definition first ty: ActionT ty (Maybe OutRes) :=
    Read top: TopEntry <- topRegName;
    LETA ftopM: Maybe InRes <- (@Fifo.Ifc.first _ fifo _);
    LETA notComplete : Bool <- isNotComplete #top #ftopM;
    LET ftop <- #ftopM @% "data";

    LET upperTopCompressed <- isCompressed (#top @% "upper" @% "data");
           
    LET retAddr: VAddr <-
      (IF isImmErr (#top @% "immRes") || isFinalErr (#top @% "error")
       then (IF #top @% "lower" @% "valid"
             then toVAddr (#top @% "vaddr")
             else (toVAddr (#top @% "vaddr")) + $2)
       else (IF #top @% "lower" @% "valid"
             then toVAddr (#top @% "vaddr")
             else (IF #upperTopCompressed
                   then (toVAddr (#top @% "vaddr")) + $2
                   else (IF #notComplete
                         then toVAddr (#top @% "vaddr" + $1)
                         else (toVAddr (#top @% "vaddr")) + $2))));

    LET retInst: Inst <-
      (IF #top @% "lower" @% "valid"
       then {< #top @% "upper" @% "data", #top @% "lower" @% "data" >}
       else (IF #upperTopCompressed
             then {< $0, #top @% "upper" @% "data" >}
             else {< UniBit (TruncLsb compInstSz compInstSz) (#ftop @% "inst"), #top @% "upper" @% "data" >}));

    LET straddle: Bool <- isStraddle #top;
    
    LET pickFifo: Bool <- (IF #straddle
                           then !(isImmErr (#top @% "immRes") || (isFinalErr (#top @% "error")))
                           else $$false);

    LET ret: OutRes <- STRUCT { "notComplete?" ::= #notComplete;
                                "vaddr" ::= #retAddr;
                                "immRes" ::= (IF #pickFifo then #ftop @% "immRes" else #top @% "immRes");
                                "error" ::= (IF #pickFifo then #ftop @% "error" else #top @% "error");
                                "compressed?" ::= isCompressed (UniBit (TruncLsb compInstSz compInstSz) #retInst);
                                "errUpper?" ::= #pickFifo;
                                "inst"  ::= #retInst};
    Ret (STRUCT { "valid" ::= #top @% "upper" @% "valid";
                  "data" ::= #ret}: Maybe OutRes @# ty).

  Local Definition deq ty: ActionT ty Bool :=
    Read top: TopEntry <- topRegName;
    LETA ftopM: Maybe InRes <- (@Fifo.Ifc.first _ fifo _);
    LETA notComplete : Bool <- isNotComplete #top #ftopM;
    LET ftop <- #ftopM @% "data";

    LET allowDeq <-
      #top @% "upper" @% "valid" &&
      ((isImmErr (#top @% "immRes") || isFinalErr (#top @% "error")) ||
       (#top @% "lower" @% "valid" && !isCompressed (#top @% "lower" @% "data")) ||
       (!(#top @% "lower" @% "valid") && !#notComplete));

    LET newLowerValid <- #ftopM @% "valid" && (* (isAligned (#ftop @% "vaddr")) && *) !(isStraddle #top);

    LET newTopRegDeq: TopEntry <- STRUCT { "vaddr"  ::= ZeroExtendTruncMsb (vAddrSz - 2) (#ftop @% "vaddr");
                                           "immRes" ::= #ftop @% "immRes";
                                           "error"  ::= #ftop @% "error";
                                           "upper"  ::= STRUCT { "valid" ::= #ftopM @% "valid";
                                                                 "data" ::= UniBit (TruncMsb compInstSz _)
                                                                                   (#ftop @% "inst")};
                                           "lower"  ::= STRUCT { "valid" ::= #newLowerValid;
                                                                 "data" ::= UniBit (TruncLsb compInstSz _)
                                                                                   (#ftop @% "inst")}
                                         };

    LET newTopRegLower: TopEntry <- #top @%[ "lower" <- STRUCT { "valid" ::= $$false;
                                                                 "data" ::= $$(getDefaultConst (Bit compInstSz)) }];
    Write topRegName <- IF #allowDeq then #newTopRegDeq else IF isCompressed (#top @% "lower" @% "data") then #newTopRegLower else #top;
    Ret #allowDeq.

  Local Definition regs
    := (makeModule_regs
          ((Register topRegName : TopEntry <- Default)
             ++ (Register outstandingName : Bit (lgSize + 1) <- Default)
             ++ (Register clearOutstandingName : Bit (lgSize + 1) <- Default))%kami ++
       (@Fifo.Ifc.regs _ fifo)).

  Definition impl: Ifc := {| Fetcher.Ifc.regs := regs;
                             Fetcher.Ifc.regFiles := Fifo.Ifc.regFiles fifo;
                             Fetcher.Ifc.isFull := isFull;
                             Fetcher.Ifc.sendAddr := sendAddr;
                             Fetcher.Ifc.callback := callback;
                             Fetcher.Ifc.deq := deq;
                             Fetcher.Ifc.first := first;
                             Fetcher.Ifc.canClear := canClear;
                             Fetcher.Ifc.clear := clear;
                             Fetcher.Ifc.notCompleteDeqRule := notCompleteDeqRule;
                             Fetcher.Ifc.transferRule := transferRule; |}.
End Impl.
