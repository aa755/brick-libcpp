Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.stdlib.allocator.spec.
Require Import bluerock.cpp.stdlib.cassert.spec.
Require Import bluerock.cpp.stdlib.vector.spec.
Require Import bluerock.cpp.stdlib.atomic.spec.
Require Import bluerock.cpp.stdlib.algorithms.spec.
Require Import bluerock.cpp.stdlib.new.spec_exc.
Require Import bluerock.brick.libcpp.newarr.spec_exc.
Require Import bluerock.brick.libcpp.newarr.hints.
Require Import bluerock.cpp.spec.concepts.
Require Import bluerock.cpp.spec.concepts.experimental.
Require Import bluerock.brick.libcpp.shared_ptr.inc_shared_ptr_cpp.
Lemma seqprefix (prelen len start: nat):
  (prelen <= len)%nat -> seq start len = (seq start prelen)++(seq (start+prelen) (len -prelen)).
Proof using.
  intros Hl.
  replace len with (prelen+(len-prelen))%nat at 1 by lia.
  rewrite seq_app.
  reflexivity.
Qed.

Definition liftQ {PROP: bi} (p: Qp->PROP) (q:Q) : PROP :=
  match toQp q with
  | None => emp
  | Some qp => p qp
  end.

Record CtrlBlockId : Set :=
  {
    contenderLocs: list gname; (* each stores a unit. N -> gname may be tricky for constructor proof *)
    dataLoc: ptr;
  }.

Open Scope N_scope.
Definition maxContention : positive. Proof. Admitted.

Definition ctrOffset: offset. Proof. Admitted.
(** offset of the field storing ownedPtr in any shared_ptr object *)
Definition ownedPtrOffset: offset. Proof. Admitted. 
(** offset of the field storing ctrlBlock pointer in any shared_ptr object *)
Definition ctrlBlockPtrOffset: offset. Proof. Admitted. 

Lemma maxContentionLb : 2^32 <= Npos maxContention. Proof. Admitted.
Definition maxContentionQp := pos_to_Qp maxContention.

Definition countLN {A : Type} (f : A -> bool) (l : list A) : N :=
  lengthN (filter f l).


Section specs.
  Context `{Σ : cpp_logic, MOD:inc_shared_ptr_cpp.module ⊧ σ}.

  Import linearity.

  Definition dynAllocatedR ty (base:ptr) : mpred :=
    Exists (bookKeepingLoc:ptr) (overhead:N),
      match (size_of _ ty) with
      | Some sz => bookKeepingLoc |-> pred.allocatedR 1 (overhead+sz)
      | None => False
      end
      **  (base |-> new_token.R 1
                {| new_token.alloc_ty := ty;
                   new_token.storage_ptr := bookKeepingLoc.["unsigned char" ! overhead];
                   new_token.overhead := overhead |}).


  Context {hf:fracG () _Σ}.

  (* just an execlusive token for each contenderid. can be defined with a simpler CMRA as fractionality is not needed. fgptsoQ has good automation support  *)
  Definition copyConstrRight ctrlid contenderid : mpred :=
    match nth_error (contenderLocs ctrlid) contenderid with
    | Some g => fgptstoQ g 1 tt
    | None => emp (* bad argument, contenderid > maxContention *)
    end.
      
  Definition allContenderIds : list nat := (seq 0 (Pos.to_nat maxContention)).
  
  (** Currently, we assume the control block is just an atomic counter.
      In reality, it is probably a struct. so move the atomicR to some defn ctrlBlockR *)
  Definition SharedPtrR (cppty: type) (id: CtrlBlockId) (Rpiece : nat -> Rep) (ownedPtr:ptr)  : Rep :=
    structR ("std::shared_ptr".<<Atype cppty>>) 1
    ** [| ([∗ list] ctid ∈ allContenderIds, Rpiece ctid) |-- anyR "int" 1 |]
    ** ownedPtrOffset |-> primR (Tptr cppty) 1 (Vptr ownedPtr)
    ** ctrlBlockPtrOffset |-> primR (Tnamed ("std::atomic".<<Atype "long">>)) 1 (Vptr (dataLoc id))
    ** [| ownedPtr<>nullptr |] (* use NullSharedPtr othewise *)
    ** [| lengthN (contenderLocs id) = Npos maxContention |]
    ** pureR (inv nroot (Exists (ctrVal:N) (pieceOut : nat ->bool) ,
         (dataLoc id),, ctrOffset |-> atomic.R "long" 1 (Z.of_N ctrVal)
         ** ([∗ list] ctid ∈ allContenderIds,
             if pieceOut ctid then copyConstrRight id ctid else ownedPtr |-> Rpiece ctid)
         ** [| countLN pieceOut allContenderIds  = ctrVal |]
         ** (if (bool_decide (ctrVal = 0))
              then emp
              else dynAllocatedR cppty ownedPtr))).

  Definition NullSharedPtrR (cppty: type) : Rep :=
    structR "shared_ptr<int>" 1
    ** ownedPtrOffset |-> primR (Tptr "cppty") 1 (Vptr nullptr)
    ** ctrlBlockPtrOffset |->  primR (Tptr "cppty") 1 (Vptr nullptr).


  Definition Lstar (l: list mpred) : mpred := [∗ list] i ∈ l, i.

  Definition allButFirstContenderId := (seq 1 (Pos.to_nat maxContention -1 )).

  Section ty.
  Context {ty:type}.

  Definition init_ctor :=
    specify {| info_name := (Nscoped ("std::shared_ptr".<<Atype ty>>) (Nctor [Tptr ty])).<<Atype ty, Atype "void">>
            ; info_type := tCtor ("std::shared_ptr".<<Atype ty>>) [Tptr ty] |} (fun (this:ptr) =>
    \arg{p:ptr} "ownedPtr" (Vptr p)
    \pre{p} dynAllocatedR "int" p
    \pre{Rpiece: nat -> Rep} [∗ list] ctid ∈ allButFirstContenderId,
      p |-> Rpiece ctid
    \pre [|([∗ list] ctid ∈ allContenderIds, Rpiece ctid)
             |-- anyR ty 1  |]
    (*           ^^ if anyR is not meaningful for non-scalar types,
                 replace this with wp of default destructor *)
    \post Exists (ctrlBlockId: CtrlBlockId),
       this |-> SharedPtrR "int"  ctrlBlockId Rpiece p
       ** ([∗ list] ctid ∈ allButFirstContenderId, copyConstrRight ctrlBlockId ctid)).

  Definition SpecFor_init_ctor := RegisterSpec init_ctor.
  #[global] Existing Instance SpecFor_init_ctor.

  

  (** move constructor. the new object represents the same piece of ownership 
  cpp.spec "std::shared_ptr<int>::shared_ptr(std::shared_ptr<int>&&)" as shm with (fun (this:ptr) =>
    \arg{other:ptr} "other" (Vptr other)
    \pre{ctrlBlockId ownedPtr Rpiece} other |-> SharedPtrR "int" ctrlBlockId Rpiece ownedPtr
    \post other  |-> NullSharedPtrR "int"
          ** this |-> SharedPtrR "int"  ctrlBlockId Rpiece ownedPtr).
 *)
  Notation spty := ("std::shared_ptr".<<Atype ty>>).
  Definition move_ctor :=
    specify.template.ctor spty [Trv_ref ((Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \pre{ctrlBlockId ownedPtr Rpiece} other |-> SharedPtrR ty ctrlBlockId Rpiece ownedPtr
    \post other  |-> NullSharedPtrR "int"
          ** this |-> SharedPtrR "int"  ctrlBlockId Rpiece ownedPtr.

  Definition SpecFor_move_ctor := RegisterSpec move_ctor.
  #[global] Existing Instance SpecFor_move_ctor.

  cpp.spec "std::shared_ptr<int>::~shared_ptr()" as shd1 with (fun (this:ptr) =>
    \with (null:bool)
    \pre{(p:ptr) (sid: if null then unit else prod CtrlBlockId nat) Rpiece}
      this |-> (match null as b return (if b then unit else prod CtrlBlockId nat) -> Rep with
                | false => fun sid=>
                             SharedPtrR "int" sid.1 Rpiece p
                             ** Rpiece sid.2
                | true => fun sid=> NullSharedPtrR "int"
                end) sid

    \post (match null as b return (if b then unit else prod CtrlBlockId nat) -> mpred with
                | false => fun sid=> copyConstrRight sid.1 sid.2
                | true => fun sid=> emp
                end) sid).

  (*
  cpp.spec "std::shared_ptr<int>::~shared_ptr()" as shd2 with (fun (this:ptr) =>
    \pre this |-> NullSharedPtrR "int"
    \post emp).
  *)

  (** Copy-ctor from non-null: consumes one contenderToken*)
  cpp.spec "std::shared_ptr<int>::shared_ptr(std::shared_ptr<int> const&)" as shc1
    with (fun (this:ptr) =>
    \arg{other:ptr} "other" (Vptr other)
    \pre{id ctid p Rpiece}
         other |-> SharedPtrR "int" id Rpiece p
         ** copyConstrRight id ctid (* this will be returned by destructor *)
    \post
         p|->Rpiece ctid ** this  |-> SharedPtrR "int" id Rpiece p
          ** other |-> SharedPtrR "int" id Rpiece p
       ).

  (** Copy-ctor from null: produces another null shared_ptr.
      No token is required. TODO: unify this spec with the spec above, using dependent types, as done in the destructor spec *)
  cpp.spec "std::shared_ptr<int>::shared_ptr(std::shared_ptr<int> const&)" as shc2
    with (fun (this:ptr) =>
    \arg{other:ptr} "other" (Vptr other)
    \pre  other |-> NullSharedPtrR "int"
    \post this  |-> NullSharedPtrR "int"
       ** other |-> NullSharedPtrR "int").


  Definition SP_acc  := ("std::__shared_ptr_access" .<< 
                           Atype "int",
                           Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy"),
                           Avalue (Eint 0 "bool"),
                           Avalue (Eint 0 "bool") >>)%cpp_name.

  Definition SP_impl := ("std::__shared_ptr" .<< 
                           Atype "int",
                           Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

  Definition SP := "std::shared_ptr<int>"%cpp_name.

  (** Reconstruct the most-derived object pointer from the base-subobject "this". *)
  Definition upcast_offset : offset :=
    (o_derived σ SP_acc SP_impl ,, o_derived σ SP_impl SP).

  cpp.spec (SP_acc.::Nop function_qualifiers.Nc OOStar []) as shg with 
    (fun (this:ptr) =>
       \prepost{id p Rpiece} this |-> upcast_offset |-> SharedPtrR "int" id Rpiece p
       \post[Vptr p] emp
       ).

  #[global] Instance sharedR_typeptr_observe ty id (p:ptr) op Rpiece
    : Observe (type_ptr (Tnamed ("std::shared_ptr".<<Atype ty>>)) p) (p|->SharedPtrR ty id Rpiece op):= _.

  Definition allPiecesAndObjs Rpiece id (ownedPtr: ptr) (pieceOut: nat->bool) : Rep :=
   ([∗ list] ctid ∈ allContenderIds,
     if pieceOut ctid
     then pureR (ownedPtr |-> Rpiece ctid)
          ** SharedPtrR "int" id Rpiece ownedPtr
     else pureR (copyConstrRight id ctid)).

  Lemma redistributePayloadOwnership {Rpieceold Rpiecenew: nat -> Rep} (pieceOut : nat -> bool) id ownedPtr:
    allPiecesAndObjs Rpieceold id ownedPtr pieceOut
      |-- allPiecesAndObjs Rpiecenew id ownedPtr pieceOut.
  Proof. Admitted.

  cpp.spec "testnew4()" as testnew4spec with (
    \pre emp
    \post{p:ptr}[Vptr p] Exists payload sid,
       p |-> SharedPtrR "int" sid (fun ctid => if bool_decide (ctid=0%nat) then anyR "int" 1 else emp) payload
       ** payload |-> intR (cQp.m 1) 1
       ** ([∗ list] ctid ∈ allButFirstContenderId,
              copyConstrRight sid ctid)
    ).


  
Lemma one_as_bigsep {PROP: bi} {A} {eqd: EqDecision A} (f  : PROP) l (x: A):
  x ∈ l ->
  NoDup l -> (* too strong: we only need x to be not duplicated *)
  f -|- ([∗ list] id ∈ l, if bool_decide (id=x) then f else emp)%I.
Proof using.
  clear MOD.
  intros.
  rewrite  -> big_op.big_sepL_difference_singleton with (x:=x) by assumption.
  simpl.
  case_bool_decide; [ | congruence].
  assert (f ** (emp)%I ≡ f) as Heq by (apply right_id; eauto with typeclass_instances).
  rewrite <- Heq at 1.
  f_equiv.
  rewrite <- big_sepL_emp with (l:=(list_difference l [x])).
  apply big_opL_proper.
  intros  ? id  Hl.
  case_decide;[ | reflexivity].
  subst.
  apply elem_of_list_lookup_2 in Hl.
  apply elem_of_list_difference in Hl.
  forward_reason.
  apply False_rect.
  simpl in *.
  set_solver.
Qed.

Hint Resolve NoDup_seq : setsolver.
Hint Rewrite elem_of_seq: equiv.
Hint Rewrite @big_sepL_emp: equiv.
Lemma allButFirstEmp : ([∗ list] x ∈ seq 1 (Pos.to_nat maxContention -1), 
       if bool_decide (x = 0%nat)
       then anyR "int" 1$m
       else emp)
                         -|- emp.
Proof using.
  erewrite  big_opL_proper with (g := fun _ _=> emp).
  2:{ intros ? ? Hl.
      apply elem_of_list_lookup_2 in Hl.
      autorewrite with equiv in Hl.
      resolveDecide lia.
      reflexivity.
  }
  autorewrite with equiv.
  reflexivity.
Qed.

End ty.
  (** proofs: *)
  Opaque SharedPtrR.
  
  Definition observeSharedType r q t Rpiece op:= @observe_fwd _ _ _ (sharedR_typeptr_observe r q t Rpiece op).

  Opaque NullSharedPtrR.
  Hint Resolve observeSharedType : br_opacity.
  Lemma prf2: verify[module] testnew4spec.
  Proof using MOD.
    verify_spec.
    pose proof maxContentionLb.
    go.
    unfold dynAllocatedR.
    iExists _.
    set (Rpiece:=(fun ctid => if bool_decide (ctid=0%nat) then anyR "int" 1 else emp)).
    iExists Rpiece.
    go.
    iExists _.
    iExists 0.
    simpl.
    eagerUnifyU.
    go.
    normalize_ptrs.
    eagerUnifyU.
    go.
    rewrite <- _at_big_sepL.
    unfold allButFirstContenderId.
    unfold Rpiece.
    rewrite allButFirstEmp. go.
    provePure.
    {
      unfold allContenderIds.
      rewrite -> seqprefix with (prelen:=1%nat) by lia.
      simpl.
      rewrite allButFirstEmp. go.
    }
    go.
    iExists _, _, Rpiece.
    unfold upcast_offset.
    normalize_ptrs.
    eagerUnifyU.
    go.
    normalize_ptrs.
    go.
    iExists _, _, Rpiece.
    eagerUnifyU.
    go.
    iExists true.
    iExists nullptr.
    iExists tt.
    iExists Rpiece.
    ego.
  Qed.
  
  Disable Notation "::wpOperand".
  
  cpp.spec "testnew()" as testnewspec with (
    \pre emp
    \post{p:ptr}[Vptr p] dynAllocatedR "int" p ** p |-> primR "int" 1 (Vint 1)
    ).

  Lemma prf: verify[module] testnewspec.
  Proof using MOD.
    verify_spec.
    go;[ego | ego |].
    unfold dynAllocatedR. go.
    ego.
    eagerUnifyU.
    normalize_ptrs.
    go.
  Qed.

End specs.
