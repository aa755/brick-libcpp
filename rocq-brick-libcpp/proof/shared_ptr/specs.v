Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.stdlib.allocator.spec.
Require Import bluerock.cpp.stdlib.cassert.spec.
Require Import bluerock.cpp.stdlib.vector.spec.
Require Import bluerock.cpp.stdlib.atomic.spec.
Require Import bluerock.cpp.stdlib.algorithms.spec.
Require Import bluerock.cpp.stdlib.new.spec_exc.
(*
./../../../../brick-libcpp/rocq-brick-libcpp/proof/dune
Require Import bluerock.cpp.stdlib.test.vector.test_cpp.
*)
Require Import bluerock.brick.libcpp.newarr.spec_exc.
Require Import bluerock.brick.libcpp.newarr.hints.
Require Import bluerock.brick.libcpp.shared_ptr.inc_shared_ptr_cpp.


Section proofs.
  Context `{Σ : cpp_logic, MOD:inc_shared_ptr_cpp.module ⊧ σ}.

  Import linearity.

  Definition dynAllocatedArrayR ty (base:ptr) : mpred :=
    Exists (bookKeepingLoc:ptr) (overhead:N),
      match (size_of _ ty) with
      | Some sz => bookKeepingLoc |-> pred.allocatedR 1 (overhead+sz)
      | None => False
      end
      **  (base |-> new_token.R 1 {| new_token.alloc_ty := ty; new_token.storage_ptr := bookKeepingLoc.["unsigned char" ! overhead]; new_token.overhead := overhead |}).

Notation dynAllocatedR := dynAllocatedArrayR.
(*
Definition dynAllocatedR ty (base:ptr) : mpred :=
  Exists (bookKeepingLoc:ptr) (overhead:N),
    match (size_of _ ty) with
    | Some sz => bookKeepingLoc |-> pred.allocatedR 1 sz
    | None => False
    end
    **  (base |-> new_token.R 1 {| new_token.alloc_ty := ty; new_token.storage_ptr := bookKeepingLoc; new_token.overhead := overhead |}).
*)

(*
cpp.spec "testnew()" as testnewspec with
    (
      \pre emp
        \post{p:ptr}[Vptr p] dynAllocatedR "int" p ** p |-> primR "int" 1 (Vint 1)
    ).

Lemma prf: verify[module] testnewspec.
Proof using MOD.
  verify_spec.
  go.
  unfold dynAllocatedR. go.
  ego.
  eagerUnifyU.
  normalize_ptrs.
  go.
Qed.
 *)

Record CtrlBlockId : Set :=
  {
    contenderLoc: gname;
    dataLoc: ptr;
  }.

Open Scope N_scope.
Definition maxContention : positive. Proof. Admitted.

Context {hf:fracG () _Σ}.
Definition ctrOffset: offset. Proof. Admitted.
(** offset of the field storing ownedPtr in any shared_ptr object *)
Definition ownedPtrOffset: offset. Proof. Admitted. 
(** offset of the field storing ctrlBlock pointer in any shared_ptr object *)
Definition ctrlBlockPtrOffset: offset. Proof. Admitted. 

Lemma maxContentionLb : 2^32 <= Npos maxContention. Proof. Admitted.

Definition liftQ {PROP: bi} (p: Qp->PROP) (q:Q) : PROP :=
  match toQp q with
  | None => emp
  | Some qp => p qp
  end.
    
(** Currently, we assume the control block is just an atomic counter. In reality, it is probably a struct. so move the atomicR to some defn ctrlBlockR *)       
Definition SharedPtrR (cppty: type) (id: CtrlBlockId) (ownedPtr:ptr)  : Rep :=
  structR ("std::shared_ptr".<<Atype cppty>>) 1
  ** ownedPtrOffset |-> primR "cppty" 1 (Vptr ownedPtr)
  ** ctrlBlockPtrOffset |-> primR "cppty" 1 (Vptr (dataLoc id))
  ** [| ownedPtr<>nullptr |] (* use NullSharedPtr othewise *)
  ** pureR (inv nroot
              (Exists ctrVal:Z,
                  (dataLoc id),, ctrOffset |-> atomic.R "long" 1 ctrVal
                  ** fgptstoQ (contenderLoc id) (ctrVal # maxContention) tt
                  ** (if (bool_decide (ctrVal = 0)) then emp else dynAllocatedR cppty ownedPtr)
              )
    ).

Definition NullSharedPtrR (cppty: type) : Rep :=
  structR "shared_ptr<int>" 1
  ** ownedPtrOffset |-> primR (Tptr "cppty") 1 (Vptr nullptr)
  ** ctrlBlockPtrOffset |->  primR (Tptr "cppty") 1 (Vptr nullptr).

Definition copyConstrRight id : mpred :=
  fgptstoQ (contenderLoc id) (1 # maxContention) tt.

Definition Lstar (l: list mpred) : mpred := [∗ list] i ∈ l, i.

(*
Definition intR := (fun q => anyR "int" (cQp.m q)).
 *)

Definition maxContentionQp := pos_to_Qp maxContention.

cpp.spec "std::shared_ptr<int>::shared_ptr<int, void>(int*)" as shp with (fun (this:ptr) =>
  \arg{p:ptr} "ownedPtr" (Vptr p)
  \pre{p} dynAllocatedR "int" p
  \post Exists (ctrlBlockId: CtrlBlockId),
     this |-> SharedPtrR "int"  ctrlBlockId p
     ** Lstar (List.repeat (copyConstrRight ctrlBlockId) (Pos.to_nat maxContention -1))
       ).


cpp.spec "std::shared_ptr<int>::shared_ptr(std::shared_ptr<int>&&)" as shm with (fun (this:ptr) =>
  \arg{other:ptr} "other" (Vptr other)
  \pre{ctrlBlockId ownedPtr} other |-> SharedPtrR "int" ctrlBlockId ownedPtr
  (* \prepost ownedPtr |-> intR (1/maxContentionQp)   frame, not needed *)
  \post other  |-> NullSharedPtrR "int"
     ** this |-> SharedPtrR "int"  ctrlBlockId ownedPtr
       ).


(** TODO: unify shd1 and shd2 using dependent types 
cpp.spec "std::shared_ptr<int>::~shared_ptr()" as shd1 with (fun (this:ptr) =>
  \with (null:bool)
  \pre{(p:ptr)} this |-> if null then NullSharedPtrR "int" else  SharedPtrR "int"  sg p
  \post contenderToken sg
   ).*)

cpp.spec "std::shared_ptr<int>::~shared_ptr()" as shd2 with (fun (this:ptr) =>
  \pre this |-> NullSharedPtrR "int"
  \post emp).

(** Copy-ctor from non-null: consumes one contenderToken,
    mints a new owning handle, and exports one 1/max share to the caller.
    Internally (in the proof), this will open the inv, do ctrVal := ctrVal+1 *)
cpp.spec "std::shared_ptr<int>::shared_ptr(std::shared_ptr<int> const&)" as shc1
  with (fun (this:ptr) =>
    \arg{other:ptr} "other" (Vptr other)
    \pre{id p}
         other |-> SharedPtrR "int" id p
      ** copyConstrRight id (* this will be returned by destructor *)
    \post
         this  |-> SharedPtrR "int" id p
      ** other |-> SharedPtrR "int" id p
       ).

(** Copy-ctor from null: produces another null shared_ptr.
    No token is required and no ownership fraction is transferred. *)
cpp.spec "std::shared_ptr<int>::shared_ptr(std::shared_ptr<int> const&)" as shc2
  with (fun (this:ptr) =>
    \arg{other:ptr} "other" (Vptr other)
    \pre  other |-> NullSharedPtrR "int"
    \post this  |-> NullSharedPtrR "int"
       ** other |-> NullSharedPtrR "int"
       ).


Definition SP_acc  := ("std::__shared_ptr_access" .<< 
                         Atype "int",
                         Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy"),
                         Avalue (Eint 0 "bool"),
                         Avalue (Eint 0 "bool") >>)%cpp_name.

Definition SP_impl := ("std::__shared_ptr" .<< 
                         Atype "int",
                         Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

Definition SP      := "std::shared_ptr<int>"%cpp_name.

(* Reconstruct the most-derived object pointer from the base-subobject "this". *)
Definition upcast_offset : offset :=
  (o_derived σ SP_acc SP_impl ,, o_derived σ SP_impl SP).

cpp.spec (("std::__shared_ptr_access" .<< 
                                                         Atype "int", 
                                                         Avalue
                                                           (Eint 2
                                                           "enum __gnu_cxx::_Lock_policy"), 
                                                         Avalue 
                                                           (Eint 0 "bool"), 
                                                         Avalue 
                                                           (Eint 0 "bool") >>)%cpp_name
                                                        .:: 
                                                        Nop function_qualifiers.Nc
                                                          OOStar []) as shg with 
    (fun (this:ptr) =>
       \prepost{id p} this |-> upcast_offset |-> SharedPtrR "int" id p
       \post[Vptr p] emp
       ).

#[global] Instance sharedR_typeptr_observe ty id (p:ptr) op
  : Observe (type_ptr (Tnamed ("std::shared_ptr".<<Atype ty>>)) p) (p|->SharedPtrR ty id op):= _.


cpp.spec "testnew4()" as testnew4spec with
    (
      \pre emp
      \post{p:ptr}[Vptr p]
        Exists payload sid,
        p |-> SharedPtrR "int" sid payload
        ** payload |-> intR (cQp.m 1) 1
        ** Lstar (repeat (copyConstrRight sid) (Pos.to_nat maxContention - 1)) 
    ).

Opaque SharedPtrR.
(*
  Lemma observeState (state_addr:ptr) q t:
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> UpdatedAccountStateR q t).
  Proof using. Admitted. *)
  
Definition observeSharedType r q t op:= @observe_fwd _ _ _ (sharedR_typeptr_observe r q t op).

Opaque NullSharedPtrR.
Hint Resolve observeSharedType : br_opacity.

    Lemma prf2: verify[module] testnew4spec.
    Proof using MOD.
      verify_spec.
      go.
      unfold dynAllocatedR.
      iExists _.
      go.
      iExists _.
      iExists 0.
      simpl.
      eagerUnifyU.
      go.
      normalize_ptrs.
      eagerUnifyU.
      go.
      iExists _, _.
      unfold upcast_offset.
      normalize_ptrs.
      eagerUnifyU.
      go.
      normalize_ptrs.
      go.
      iExists _, _.
      eagerUnifyU.
      go.
      iExists _,_.
      go.
    Qed.
    
    Disable Notation "::wpOperand".
  
  
