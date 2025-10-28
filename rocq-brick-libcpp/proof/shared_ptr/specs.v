(** Specs of shared_ptr.
We do not cover interaction with weak_ptr.
We cover the following usage:
- after dynamically allocating a new object (using new or new[]), it is immediately passed to the init constructor of shared_ptr (spec in init_ctor bwlow). At this time, the caller's proof needs to come up with [Rpiece: nat->Rep], defining how the ownership of this newly allocated object will be split between various shared_ptr objects that refer to it. They pass in all pieces and get back the 0th piece: [Rpiece 0] and tokens [copyConstrRight ctrlid 1 ... copyConstrRight ctrlid (maxContention-1)]  which the clients can use to make further copies of the returnes shared_ptr object. The last argument of [copyConstrRight] is the piece id. [ctrlid] identifies a single protection unit (payload object pointer) that is reference counted. The name comes from the implementation using a dynamically allocated "control block" which has an atomic counter to track how many times the copy constructor has been called - number of such objects that have already been delected.
To ensure the destructor proof goes through, the iniit ctor : [ [∗ list] ctid ∈ allContenderIds, Rpiece ctid) |-- anyR ty 1].
The pieces may not always be fractional ownerships of an object (e.g. int). For example, when the shared_ptr protects an array, it is common to have every piece own an index of the array, so that different shared_ptr objects can be used to write to different indices concurrently.

- To gain confidence in the provability of these specs, we sketch a definition of [SharedPtrR]. The invariant definition is interesting there: it stores all the [Rpeice] and [copyConstrRight] ownerships that need to be dished out later or to be used for deletion when the reference count goes to 0.
Because bluerock only supports SC atomics, the proof only works as if the stdlib implementation used SC atomics or had sufficient barriers.

- when calling the copy constructor, the caller proof has to come up with their pieceid (< maxContention) and give up
[copyConstrRight ctrlid pieceid], which they only get back when the newly constructed object is deleted.
They get [Rpiece pieceid] in return: their piece of the ownership of the the payload object.
The control block id (representing the location of the atomic refereence counter) remains the same.
The proof will atomically increment the counter to take out the Rpiece from the invariant.

- There is another Rep predicate: [NullSharedPtrR]: for the case when the shared ptr represents a dummy null ptr, e.g. after a move constructor transfers away the ownerships to a new object.

- These specs in this file allow you to change the ownership split protocol (between the various shared_ptr objects protecting the same payload object ptr) lateron (see lemma [redistributePayloadOwnership]), as long as the caller can cough up all pieces and objects associated with the payload (see [allPiecesAndObjs]).
A common pattern where this can be useful is when the thread that calls new needs to initialize the object after wrapping it in a shared_ptr but before sharing it with other concurrent threads. So until that event, it will have the execlusive ownership of the entire object (Rpeice n = emp for n>0, Rpiece 0= objR 1) and later, we redistribute with (Rpiece n => objR (1/N)).

*)

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.stdlib.allocator.spec.
Require Import bluerock.cpp.stdlib.cassert.spec.
Require Import bluerock.cpp.stdlib.vector.spec.
Require Import bluerock.cpp.stdlib.atomic.spec.
Require Import bluerock.cpp.stdlib.algorithms.spec.
Require Import bluerock.cpp.stdlib.new.spec_exc.
Require Import bluerock.brick.libcpp.newarr.spec_exc.
Require Import bluerock.brick.libcpp.newarr.hints.
Require Import bluerock.brick.libcpp.newarr.test. (* TODO move [dynAllocatedR] to a non-test file *)
Require Import bluerock.cpp.spec.concepts.
Require Import bluerock.cpp.spec.concepts.experimental.
Require Import bluerock.brick.libcpp.shared_ptr.inc_shared_ptr_cpp.


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
Definition allContenderIds : list nat := (seq 0 (Pos.to_nat maxContention)).
Definition allButFirstContenderId := (seq 1 (Pos.to_nat maxContention -1 )).

Definition countLN {A : Type} (f : A -> bool) (l : list A) : N :=
  lengthN (filter f l).

Section specs.
  Context `{Σ : cpp_logic, MOD:inc_shared_ptr_cpp.module ⊧ σ}
  {hf:fracG () _Σ} (ty:type).

  Import linearity.


  (* just an execlusive token for each contenderid. can be defined with a simpler CMRA as fractionality is not needed. fgptsoQ has good automation support  *)
  Definition copyConstrRight ctrlid contenderid : mpred :=
    match nth_error (contenderLocs ctrlid) contenderid with
    | Some g => fgptstoQ g 1 tt
    | None => emp (* bad argument, contenderid > maxContention *)
    end.
      

  Definition sptrInv (id: CtrlBlockId) (Rpiece : nat -> Rep) (ownedPtr:ptr) (pieceOut : nat ->bool) :=
    let ctrVal := countLN pieceOut allContenderIds in
    (dataLoc id),, ctrOffset |-> atomic.R "long" 1 (Z.of_N ctrVal)
         ** (if (bool_decide (ctrVal = 0))
              then emp
              else dynAllocatedR ty ownedPtr
                    ** ([∗ list] ctid ∈ allContenderIds,
                      if pieceOut ctid then copyConstrRight id ctid else ownedPtr |-> Rpiece ctid)).
  
  (** Currently, we assume the control block is just an atomic counter.
      In reality, it is probably a struct. so move the atomicR to some defn ctrlBlockR *)
  Definition SharedPtrR (id: CtrlBlockId) (Rpiece : nat -> Rep) (ownedPtr:ptr)  : Rep :=
    structR ("std::shared_ptr".<<Atype ty>>) 1
    ** [| ([∗ list] ctid ∈ allContenderIds, Rpiece ctid) |-- anyR ty 1 |]
    ** ownedPtrOffset |-> primR (Tptr ty) 1 (Vptr ownedPtr)
    ** ctrlBlockPtrOffset |-> primR (Tptr (Tnamed ("std::atomic".<<Atype "long">>))) 1 (Vptr (dataLoc id))
    ** [| ownedPtr<>nullptr |] (* use NullSharedPtr othewise *)
    ** [| lengthN (contenderLocs id) = Npos maxContention |]
    ** pureR (inv nroot (Exists (pieceOut : nat ->bool), sptrInv id Rpiece ownedPtr pieceOut)).

  Definition NullSharedPtrR : Rep :=
    structR ("std::shared_ptr".<<Atype ty>>) 1
    ** ownedPtrOffset |-> primR (Tptr ty) 1 (Vptr nullptr)
    ** ctrlBlockPtrOffset |->  primR (Tptr (Tnamed ("std::atomic".<<Atype "long">>))) 1 (Vptr nullptr).


  Definition init_ctor :=
    specify {| info_name := (Nscoped ("std::shared_ptr".<<Atype ty>>) (Nctor [Tptr ty])).<<Atype ty, Atype "void">>
            ; info_type := tCtor ("std::shared_ptr".<<Atype ty>>) [Tptr ty] |} (fun (this:ptr) =>
    \arg{p:ptr} "ownedPtr" (Vptr p)
    \pre{p} dynAllocatedR ty p
    \pre{Rpiece: nat -> Rep} [∗ list] ctid ∈ allButFirstContenderId,
      p |-> Rpiece ctid
    \pre [|([∗ list] ctid ∈ allContenderIds, Rpiece ctid)
             |-- anyR ty 1  |]
    (*           ^^ if anyR is not meaningful for non-scalar types,
                 replace this with wp of default destructor *)
    \post Exists (ctrlBlockId: CtrlBlockId),
       this |-> SharedPtrR ctrlBlockId Rpiece p
       ** ([∗ list] ctid ∈ allButFirstContenderId, copyConstrRight ctrlBlockId ctid)).

  Definition SpecFor_init_ctor := RegisterSpec init_ctor.
  #[global] Existing Instance SpecFor_init_ctor.

  Notation spty := ("std::shared_ptr".<<Atype ty>>).
  Definition move_ctor :=
    specify.template.ctor spty [Trv_ref ((Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \pre{ctrlBlockId ownedPtr Rpiece} other |-> SharedPtrR ctrlBlockId Rpiece ownedPtr
    \post other  |-> NullSharedPtrR
          ** this |-> SharedPtrR ctrlBlockId Rpiece ownedPtr.

  Definition SpecFor_move_ctor := RegisterSpec move_ctor.
  #[global] Existing Instance SpecFor_move_ctor.

  Definition dtor_spec :=
    specify.template.dtor spty $
    \this this
    \pre{(null:bool) (p:ptr) (sid: if null then unit else prod CtrlBlockId nat) Rpiece}
      this |-> (match null as b return (if b then unit else prod CtrlBlockId nat) -> Rep with
                | false => fun sid=>
                             SharedPtrR sid.1 Rpiece p
                             ** Rpiece sid.2
                | true => fun sid=> NullSharedPtrR
                end) sid

    \post (match null as b return (if b then unit else prod CtrlBlockId nat) -> mpred with
                | false => fun sid=> copyConstrRight sid.1 sid.2
                | true => fun sid=> emp
                end) sid.
  
  Definition SpecFor_dtor := RegisterSpec dtor_spec.
  #[global] Existing Instance SpecFor_dtor.


  Definition copy_ctor :=
    specify.template.ctor spty [Tref (Tconst (Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \pre{id ctid p Rpiece} other |-> SharedPtrR id Rpiece p
    \pre copyConstrRight id ctid (* this will be returned by destructor *)
    \pre [| N.of_nat ctid < Npos maxContention|]%N
    \post
         p|->Rpiece ctid ** this  |-> SharedPtrR id Rpiece p
          ** other |-> SharedPtrR id Rpiece p.
                          
  Definition SpecFor_copy_ctor := RegisterSpec copy_ctor.
  #[global] Existing Instance SpecFor_copy_ctor.

  (** Copy-ctor from null: produces another null shared_ptr.
      No token is required. TODO: unify this spec with the spec above, using dependent types, as done in the destructor spec *)
  Definition copy_ctor_null :=
    specify.template.ctor spty [Tref (Tconst (Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \pre other |-> NullSharedPtrR
    \post this  |-> NullSharedPtrR
          ** other |-> NullSharedPtrR.
               

  Definition SP_acc  := ("std::__shared_ptr_access" .<< 
                           Atype ty,
                           Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy"),
                           Avalue (Eint 0 "bool"),
                           Avalue (Eint 0 "bool") >>)%cpp_name.

  Definition SP_impl := ("std::__shared_ptr" .<< 
                           Atype ty,
                           Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

  (** Reconstruct the most-derived object pointer from the base-subobject "this". *)
  Definition upcast_offset : offset :=
    (o_derived σ SP_acc SP_impl ,, o_derived σ SP_impl spty).

  Definition deref :=
    specify.template.op SP_acc OOStar function_qualifiers.Nc (Tref ty) [] $
       \this this
       \prepost{id p Rpiece} this |-> upcast_offset |-> SharedPtrR id Rpiece p
       \post[Vref p] emp.

  Definition SpecFor_deref := RegisterSpec deref.
  #[global] Existing Instance SpecFor_deref.
  
  #[global] Instance sharedR_typeptr_observe id (p:ptr) op Rpiece
    : Observe (type_ptr (Tnamed ("std::shared_ptr".<<Atype ty>>)) p) (p|->SharedPtrR id Rpiece op):= _.
  

  Definition allPiecesAndObjs Rpiece id (ownedPtr: ptr) (pieceOut: nat->bool) : Rep :=
   ([∗ list] ctid ∈ allContenderIds,
     if pieceOut ctid
     then pureR (ownedPtr |-> Rpiece ctid)
          ** pureR (Exists (base:ptr), base |->SharedPtrR id Rpiece ownedPtr)
     else pureR (copyConstrRight id ctid)).

  Lemma redistributePayloadOwnership {Rpieceold Rpiecenew: nat -> Rep} (pieceOut : nat -> bool) id ownedPtr:
    allPiecesAndObjs Rpieceold id ownedPtr pieceOut
      |-- allPiecesAndObjs Rpiecenew id ownedPtr pieceOut.
  Proof. Admitted.


End specs.


Hint Resolve NoDup_seq : setsolver.
Hint Rewrite elem_of_seq: equiv.
Hint Rewrite @big_sepL_emp: equiv.

Lemma seqprefix (prelen len start: nat):
  (prelen <= len)%nat -> seq start len = (seq start prelen)++(seq (start+prelen) (len -prelen)).
Proof using.
  intros Hl.
  replace len with (prelen+(len-prelen))%nat at 1 by lia.
  rewrite seq_app.
  reflexivity.
Qed.
  
Lemma one_as_bigsep {PROP: bi} {A} {eqd: EqDecision A} (f  : PROP) l (x: A):
  x ∈ l ->
  NoDup l -> (* too strong: we only need x to be not duplicated *)
  f -|- ([∗ list] id ∈ l, if bool_decide (id=x) then f else emp)%I.
Proof using.
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

Section proofs.
  (** proofs: *)
  Opaque SharedPtrR.
  Context `{Σ : cpp_logic, MOD:inc_shared_ptr_cpp.module ⊧ σ}
  {hf:fracG () _Σ}.
  
  Definition observeSharedType r q t Rpiece op:= @observe_fwd _ _ _ (sharedR_typeptr_observe r q t Rpiece op).

  cpp.spec "testnew4()" as testnew4spec with (
    \pre emp
    \post{p:ptr}[Vptr p] Exists payload sid,
       p |-> SharedPtrR "int" sid (fun ctid => if bool_decide (ctid=0%nat) then anyR "int" 1 else emp) payload
       ** payload |-> intR (cQp.m 1) 1
       ** ([∗ list] ctid ∈ allButFirstContenderId,
              copyConstrRight sid ctid)
    ).



  Lemma allButFirstEmp ty : ([∗ list] x ∈ seq 1 (Pos.to_nat maxContention -1), 
       if bool_decide (x = 0%nat)
       then anyR ty 1$m
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
  
  Opaque NullSharedPtrR.
  Hint Resolve observeSharedType : br_opacity.
  Print SpecFor_copy_ctor.
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
End proofs.
