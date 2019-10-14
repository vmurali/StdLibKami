(* Implements the Pseudo Least Recently Used Algorithm. *)
Require Import Wf.
Require Import Wf_nat.
Require Import Kami.AllNotations.

Section lru.
  Open Scope kami_expr.
  Open Scope kami_action.

  (*
    the number of data registers.
    Note: should be of the form 2^n for some n.
  *)
  Variable num : nat.

 (* the type of data stored in the registers *)
  Variable Data : Kind.

  (* the name of the register that stores the path of the least recently used data register *)
  Variable stateRegName : string.

  (*
    Note: the number of internal nodes in the balanced binary tree is [num - 1].
  *)
  Definition stateWidth := (num - 1)%nat.

  (* represents the state of the Lru unit - i.e. the value of each node within the state tree. *)
  Definition State := Array stateWidth Bool.

  (*
    Note: the total number nodes and leaves in the tree is [2*num - 1].
  *)
  Definition labelWidth := Nat.log2_up (2 * num - 1)%nat.

  Definition Label := Bit labelWidth.

  Definition indexWidth := Nat.log2_up num.

  Definition Index := Bit indexWidth.

  Section ty.
    Variable ty : Kind -> Type.

    Definition labelIndex
      (label : Label @# ty)
      :  Index @# ty
      := ~(ZeroExtendTruncLsb indexWidth label + $1).

    Fixpoint getVictimAux
      (depth : nat)
      (state : State @# ty)
      (label : Label @# ty)
      :  Pair Index State ## ty
      := LETC index : Index <- labelIndex label;
         LETC dir : Bool <- state@[ZeroExtendTruncLsb stateWidth #index];
         match depth with
         | 0
           => RetE (STRUCT {
                "fst" ::= #index;
                "snd" ::= state
                } : Pair Index State @# ty)
         | S depth'
           => LETE result
                :  Pair Index State
                <- getVictimAux depth'
                     (state@[#index <- !#dir])
                     (IF #dir
                       then (label << ($1 : Bit 1 @# ty)) | $1 (* left child's label *)
                       else (label << ($1 : Bit 1 @# ty)));    (* right child's label *)
              RetE
                (IF #index >= $(num - 1)
                  then
                    (STRUCT {
                       "fst" ::= #index;
                       "snd" ::= state
                     } : Pair Index State @# ty)
                  else #result)
         end.

    (* The maximum depth of the balanced tree. *)
    Definition depth := Nat.log2_up num.

    (* The root node label. *)
    Definition rootLabel : Label @# ty := $$(wones labelWidth) << ($1 : Bit 1 @# ty).

    (* Returns the index of the least recently used register *)
    Definition getVictim
      :  ActionT ty Index
      := Read state : State <- stateRegName;
         LETA result
           :  Pair Index State
           <- convertLetExprSyntax_ActionT
                (getVictimAux depth #state rootLabel);
         Write stateRegName : State <- #result @% "snd";
         Ret (#result @% "fst").

    Definition indexLabel
      (index : Index @# ty)
      :  Label @# ty
      := (~ (ZeroExtendTruncLsb labelWidth index)) - $1.

    (* Note: label must not be the root or the dual of the root - i.e. labelIndex label != 0 *)
    Definition parentLabel
      (label : Label @# ty)
      :  Label @# ty
      := OneExtendTruncLsb labelWidth
           (ZeroExtendTruncMsb (labelWidth - 1) label).

    Fixpoint accessAuxRec
      (maxDepth : nat)
      (state : State @# ty)
      (label : Label @# ty)
      (dir : Bool @# ty)
      :  State ## ty
      := match maxDepth with
         | 0 => RetE state (* impossible case - bounding recursion. *)
         | S depth
           => LETC index : Index <- labelIndex label;
              LETC nextState : State <- state@[#index <- dir];
              LETE result : State
                <- accessAuxRec depth #nextState (parentLabel label)
                     (ZeroExtendTruncLsb 1 label == $0);
              RetE
                (IF label == rootLabel
                  then #nextState
                  else #result)
         end.

    Definition accessAux
      (state : State @# ty)
      (index : Index @# ty)
      :  State ## ty
      := LETC rawLabel : Label <- indexLabel index;
         LETC label : Label
           <- IF #rawLabel == rootLabel
               then #rawLabel << ($1 : Bit 1 @# ty) >> ($1 : Bit 1 @# ty) (* set msb to 0 *)
               else #rawLabel;
         accessAuxRec depth state
           (parentLabel #label)
           (ZeroExtendTruncLsb 1 #label == $0).

    (* updates the least recently used data to point away from the given register. *)
    Definition access
      (index : Index @# ty)
      :  ActionT ty Void
      := Read state : State <- stateRegName;
         LETA result : State <- convertLetExprSyntax_ActionT (accessAux #state index);
         Write stateRegName : State <- #result;
         Retv.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.
End lru.

Section tests.

  Open Scope kami_expr.

  Local Definition T := Const type true.
  Local Definition F := Const type false.

  Definition testGetVictim
    (num : nat)
    (state : State num @# type)
    (expected : word (indexWidth num))
    :  Prop
    := (evalLetExpr
         (LETE result
           : Pair (Index num) (State num)
           <- getVictimAux
                (depth num)
                state
                (rootLabel num type);
          RetE ((Var type (SyntaxKind _) result) @% "fst"))) =
        expected.

  Goal testGetVictim (num := 3) (ARRAY {T; T}) $3. Proof ltac:(reflexivity). 
  Goal testGetVictim (num := 3) (ARRAY {T; F}) $0. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 3) (ARRAY {F; T}) $2. Proof ltac:(reflexivity).

  Goal testGetVictim (num := 6) (ARRAY {T; T; T; T; T}) $7. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {F; T; T; T; T}) $5. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {F; T; F; T; T}) $6. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {T; F; T; T; F}) $2. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {T; F; T; T; T}) $1. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {T; T; T; F; T}) $0. Proof ltac:(reflexivity).

  Goal testGetVictim (num := 7) (ARRAY {T; T; T; T; T; T}) $7. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {T; T; T; F; T; T}) $0. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {T; F; F; T; T; T}) $1. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {T; F; T; T; F; T}) $2. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {F; T; T; T; T; T}) $3. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {F; T; T; T; T; F}) $4. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {F; T; F; T; T; T}) $6. Proof ltac:(reflexivity).

  Goal (evalExpr (indexLabel (num := 5) (Const type (natToWord _ 7)))) = natToWord _ 7. Proof. reflexivity. Qed.
  Goal (evalExpr (indexLabel (num := 5) (Const type (natToWord _ 4)))) = 4'b"1010". Proof. reflexivity. Qed.
  Goal (evalExpr (parentLabel (num := 5) (Const type (4'b"1010")))) = 4'b"1101". Proof. reflexivity. Qed.
  Goal (evalExpr (parentLabel (num := 5) (Const type (4'b"1001")))) = 4'b"1100". Proof. reflexivity. Qed.
  Goal (evalExpr (parentLabel (num := 5) (Const type (4'b"0110")))) = 4'b"1011". Proof. reflexivity. Qed.
  Goal (evalExpr (parentLabel (num := 5) (Const type (4'b"0111")))) = 4'b"1011". Proof. reflexivity. Qed.

  Definition evalArray
    (k : Kind)
    (n : nat)
    :  Array n k ## type -> list (type k)
    := match n return Array n k ## type -> list (type k) with
       | 0 => fun _ => []
       | S n
         => nat_rect
              (fun m : nat
                => m < (S n) -> Array (S n) k ## type -> list (type k))
              (fun (H : 0 < (S n)) xs
                => [(evalLetExpr xs) (Fin.of_nat_lt H)])
              (fun m F (H : S m < (S n)) xs
                => (F (Nat.lt_succ_l m (S n) H) xs) ++
                   [(evalLetExpr xs) (Fin.of_nat_lt H)])
              n (Nat.lt_succ_diag_r n)
      end%nat.

  Definition testAccess
    (num : nat)
    (state : State num @# type)
    (index : Index num @# type)
    (expected : list bool)
    :  Prop
    := evalArray (accessAux (num := num) state index) = expected.

  Goal testAccess (num := 2) (ARRAY {T}) (Const type (1'b"0")) [true]. Proof ltac:(reflexivity).
  Goal testAccess (num := 2) (ARRAY {T}) (Const type (1'b"1")) [false]. Proof ltac:(reflexivity).
  Goal testAccess (num := 3) (ARRAY {T; T}) (Const type (2'b"11")) [false; false]. Proof ltac:(reflexivity).
  Goal testAccess (num := 3) (ARRAY {T; T}) (Const type (2'b"00")) [false; true]. Proof ltac:(reflexivity).
  Goal testAccess (num := 3) (ARRAY {T; T}) (Const type (2'b"10")) [true; true]. Proof ltac:(reflexivity).

  Close Scope kami_expr.

End tests.