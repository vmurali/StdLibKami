Require Import Kami.AllNotations.
Require Import Kami.Utila.

Local Open Scope kami_expr.
Local Open Scope kami_action.

Definition Struct_RegReads' ty n (sk: Fin.t n -> string * Kind) : ActionT ty (Struct sk) :=
  fold_left (fun acc i =>
               LETA tmp <- acc;
                 Read val: snd (sk i) <- fst (sk i);
                 Ret (UpdateStruct #tmp i #val))%kami_action
            (getFins n) (Ret (Const ty (getDefaultConst (Struct sk)))).

Definition Struct_RegWrites' ty n (sk: Fin.t n -> string * Kind) (e: Struct sk @# ty): ActionT ty Void :=
  fold_left (fun acc i =>
               LETA _ <- acc;
                 Write (fst (sk i)) : snd (sk i) <- ReadStruct e i ;
                 Retv)
            (getFins n) Retv.

Definition Struct_RegReads ty k: ActionT ty k :=
  match k return ActionT ty k with
  | Struct _ ski => Struct_RegReads' ty ski
  | Bool => Ret (Const ty Default)
  | Bit n => Ret (Const ty Default)
  | Array n k => Ret (Const ty Default)
  end.

Definition Struct_RegWrites ty k (e: k @# ty): ActionT ty Void:=
  match k return k @# ty -> ActionT ty Void with
  | Struct _ ski => fun e => Struct_RegWrites' e
  | Bool => fun _ => Retv
  | Bit n => fun _ => Retv
  | Array n k => fun _ => Retv
  end e.

Definition MayStruct_RegReads' ty n (s: Fin.t n -> string) (vals: Fin.t n -> {k: Kind & option (ConstT k)}):
  ActionT ty (Struct (fun i => (s i, projT1 (vals i)))) :=
  fold_left (fun (acc: ActionT ty (Struct (fun i => (s i, projT1 (vals i))))) i =>
               LETA tmp <- acc;
                 match projT2 (vals i) with
                 | Some uval =>
                   LET val: projT1 (vals i) <- Const ty uval;
                     Ret (UpdateStruct #tmp i #val)
                 | None =>
                   Read val : projT1 (vals i) <- s i;
                     Ret (UpdateStruct #tmp i #val)
                 end)%kami_action
            (getFins n) (Ret (Const ty Default)).
  
Definition MayStruct_RegWrites' ty n (s: Fin.t n -> string) (vals: Fin.t n -> {k: Kind & option (ConstT k)})
  (e: Struct (fun i => (s i, projT1 (vals i))) @# ty):
  ActionT ty Void :=
  fold_left (fun acc i =>
               LETA _ <- acc;
                 match projT2 (vals i) with
                 | Some uval =>
                   Retv
                 | None =>
                   Write (s i) : projT1 (vals i) <- ReadStruct e i ;
                     Retv
                 end)%kami_action
            (getFins n) Retv.
Local Close Scope kami_action.
Local Close Scope kami_expr.

Declare Scope kami_maystruct_scope.
Notation "name :: ty" := (name%string, existT (fun k => option (ConstT k)) ty None) (only parsing) : kami_maystruct_scope.
Notation "name ::# ty #:: val " := (name%string, existT (fun k => option (ConstT k)) ty (Some val))
                                      (only parsing, at level 99): kami_maystruct_scope.

Delimit Scope kami_maystruct_scope with kami_maystruct.

Record MayStruct n := { vals  : Fin.t n -> {k: Kind & option (ConstT k)} ;
                        names : Fin.t n -> string }.

Definition getMayStruct ls: MayStruct (length ls) :=
  {| vals  := fun i => snd (nth_Fin ls i) ;
     names := fun i => fst (nth_Fin ls i)
  |}.

Notation "'MAYSTRUCT' { s1 ; .. ; sN }" :=
  (getMayStruct (cons s1%kami_maystruct .. (cons sN%kami_maystruct nil) ..)).

Definition MayStruct_RegReads ty n (v: MayStruct n) := MayStruct_RegReads' ty (names v) (vals v).
Definition MayStruct_RegWrites (ty: Kind -> Type) n (v: MayStruct n) e := @MayStruct_RegWrites' ty n (names v) (vals v) e.





(* Definition MayStruct_RegReads' ty n (k: Fin.t n -> Kind) (s: Fin.t n -> string) (vals: forall i, option (ConstT (k i))): *)
(*   ActionT ty (Struct k s) := *)
(*   fold_left (fun acc i => *)
(*                LETA tmp <- acc; *)
(*                  match vals i with *)
(*                  | Some uval => *)
(*                    LET val : (k i) <- $$ uval; *)
(*                      Ret (UpdateStruct #tmp i #val) *)
(*                  | None => *)
(*                    Read val : (k i) <- s i; *)
(*                      Ret (UpdateStruct #tmp i #val) *)
(*                  end)%kami_action *)
(*             (getFins n) (Ret (Const ty (getDefaultConst (Struct _ _)))). *)
  
(* Definition MayStruct_RegWrites' ty n (k: Fin.t n -> Kind) (s: Fin.t n -> string) (vals: forall i, option (ConstT (k i))) *)
(*   (e: Struct k s @# ty): *)
(*   ActionT ty Void := *)
(*   fold_left (fun acc i => *)
(*                LETA _ <- acc; *)
(*                  match vals i with *)
(*                  | Some uval => *)
(*                    Retv *)
(*                  | None => *)
(*                    Write (s i) : (k i) <- ReadStruct e i ; *)
(*                      Retv *)
(*                  end)%kami_action *)
(*             (getFins n) Retv. *)

