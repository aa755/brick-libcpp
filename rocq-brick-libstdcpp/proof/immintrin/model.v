(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Set Default Goal Selector "!".

Require Import Stdlib.ZArith.BinInt.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.list.

(** * Pure Gallina model of 128-bit SSE2/SSSE3 and 256-bit AVX2 byte-vector operations *)

Definition vec128_wf (bs : list N) : Prop :=
  length bs = 16%nat /\ List.Forall (fun b => (b < 256)%N) bs.

Definition vec256_wf (bs : list N) : Prop :=
  length bs = 32%nat /\ List.Forall (fun b => (b < 256)%N) bs.

Definition sbyte_of_N (b : N) : Z :=
  if bool_decide (b < 128)%N then Z.of_N b else (Z.of_N b - 256)%Z.

Definition avx2_setzero_si256 : list N :=
  repeat 0%N 32%nat.

Definition sse2_set1_epi8 (b : N) : list N :=
  repeat (b mod 256)%N 16%nat.

Definition avx2_set1_epi8 (b : N) : list N :=
  repeat (b mod 256)%N 32%nat.

Definition avx2_setr_epi8 (bs : list N) : list N :=
  (fun b => (b mod 256)%N) <$> bs.

Definition avx2_cmpeq_epi8 (a b : list N) : list N :=
  zip_with (fun x y => if bool_decide (x = y) then 255%N else 0%N) a b.

Definition avx2_add_epi8 (a b : list N) : list N :=
  zip_with (fun x y => ((x + y) mod 256)%N) a b.

Definition avx2_sub_epi8 (a b : list N) : list N :=
  zip_with (fun x y => ((x + 256 - y mod 256) mod 256)%N) a b.

Definition sse2_sub_epi8 (a b : list N) : list N :=
  avx2_sub_epi8 a b.

Definition avx2_cmpgt_epi8 (a b : list N) : list N :=
  zip_with
    (fun x y =>
       if bool_decide (sbyte_of_N (x mod 256) > sbyte_of_N (y mod 256))%Z
       then 255%N
       else 0%N)
    a b.

Definition avx2_max_epu8 (a b : list N) : list N :=
  zip_with N.max a b.

Definition sse2_max_epu8 (a b : list N) : list N :=
  avx2_max_epu8 a b.

Definition avx2_max_epi8 (a b : list N) : list N :=
  zip_with
    (fun x y =>
       if bool_decide (sbyte_of_N (x mod 256) >= sbyte_of_N (y mod 256))%Z
       then (x mod 256)%N
       else (y mod 256)%N)
    a b.

(** 128-bit in-lane byte shuffle ([pshufb] / [_mm_shuffle_epi8]):
    bit 7 of control byte [m] zeroes the lane; otherwise low nibble [m mod 16]
    indexes into [a]. *)
Definition ssse3_shuffle_epi8 (a mask : list N) : list N :=
  (fun m =>
     if N.testbit m 7
     then 0%N
     else (default 0%N (a !! N.to_nat (m mod 16)) mod 256)%N) <$> mask.

(** 256-bit in-lane byte shuffle ([vpshufb] / [_mm256_shuffle_epi8]):
    operates independently within the low and high 128-bit halves. *)
Definition avx2_shuffle_epi8 (a mask : list N) : list N :=
  ssse3_shuffle_epi8 (take 16 a) (take 16 mask) ++
  ssse3_shuffle_epi8 (drop 16 a) (drop 16 mask).

(** Variable byte blend ([vpblendvb] / [_mm256_blendv_epi8]):
    selects [v2] where bit 7 of [mask] is 1, and [v1] otherwise. *)
Definition avx2_blendv_epi8 (v1 v2 mask : list N) : list N :=
  zip_with
    (fun xy m => if N.testbit m 7 then snd xy else fst xy)
    (zip v1 v2) mask.

Definition avx2_and_si256 (a b : list N) : list N :=
  zip_with N.land a b.

Definition avx2_or_si256 (a b : list N) : list N :=
  zip_with N.lor a b.

Definition avx2_xor_si256 (a b : list N) : list N :=
  zip_with N.lxor a b.

Definition avx2_castsi256_si128 (v : list N) : list N :=
  take 16 v.

Definition avx2_extracti128_si256 (v : list N) (imm : Z) : list N :=
  if bool_decide (Z.odd imm) then take 16 (drop 16 v) else take 16 v.

Definition avx2_set_m128i (hi lo : list N) : list N :=
  lo ++ hi.

Fixpoint movemask_bytes (bs : list N) : N :=
  match bs with
  | [] => 0%N
  | b :: rest =>
      if N.testbit b 7
      then (2 * movemask_bytes rest + 1)%N
      else (2 * movemask_bytes rest)%N
  end.

Definition avx2_movemask_epi8 (bs : list N) : N :=
  movemask_bytes bs.

(** * Well-formedness and bit/lane characterization lemmas *)

Lemma Forall_repeat_lt256 (b : N) (k : nat) :
  (b < 256)%N ->
  List.Forall (fun x => (x < 256)%N) (repeat b k).
Proof.
  intros Hb.
  induction k as [|k IH]; simpl; constructor; assumption.
Qed.

#[local] Lemma Forall_take_gen {A : Type} (P : A -> Prop) (n : nat) (xs : list A) :
  List.Forall P xs ->
  List.Forall P (take n xs).
Proof.
  intros Hxs. revert n.
  induction Hxs as [|x xs Hx _ IH]; intros [|m]; simpl; constructor; auto.
Qed.

#[local] Lemma Forall_drop_gen {A : Type} (P : A -> Prop) (n : nat) (xs : list A) :
  List.Forall P xs ->
  List.Forall P (drop n xs).
Proof.
  intros Hxs. revert n.
  induction Hxs as [|x xs Hx Hxs' IH]; intros [|m]; simpl;
    [constructor | constructor | constructor; assumption | apply IH].
Qed.

Lemma vec256_wf_setzero :
  vec256_wf avx2_setzero_si256.
Proof.
  split; [apply repeat_length | apply Forall_repeat_lt256; lia].
Qed.

Lemma vec128_wf_set1 (b : N) :
  vec128_wf (sse2_set1_epi8 b).
Proof.
  split; [apply repeat_length | apply Forall_repeat_lt256, N.mod_lt; lia].
Qed.

Lemma vec256_wf_set1 (b : N) :
  vec256_wf (avx2_set1_epi8 b).
Proof.
  split; [apply repeat_length | apply Forall_repeat_lt256, N.mod_lt; lia].
Qed.

Lemma vec256_wf_setr (bs : list N) :
  length bs = 32%nat ->
  vec256_wf (avx2_setr_epi8 bs).
Proof.
  intros Hlen. split.
  - unfold avx2_setr_epi8. by rewrite length_fmap.
  - unfold avx2_setr_epi8. clear Hlen.
    induction bs as [|b rest IH]; simpl; constructor; [apply N.mod_lt; lia | exact IH].
Qed.

Lemma avx2_set1_epi8_small (b : N) :
  (b < 256)%N ->
  avx2_set1_epi8 b = repeat b 32%nat.
Proof.
  intros Hb. unfold avx2_set1_epi8.
  rewrite N.mod_small; [reflexivity | exact Hb].
Qed.

Lemma sse2_set1_epi8_small (b : N) :
  (b < 256)%N ->
  sse2_set1_epi8 b = repeat b 16%nat.
Proof.
  intros Hb. unfold sse2_set1_epi8.
  rewrite N.mod_small; [reflexivity | exact Hb].
Qed.

Lemma zip_with_length_gen {A B C : Type} (f : A -> B -> C) (a : list A) (b : list B) :
  length (zip_with f a b) = Nat.min (length a) (length b).
Proof.
  revert b.
  induction a as [|x xs IH]; intros [|y ys]; simpl;
    [reflexivity | reflexivity | reflexivity |].
  f_equal. apply IH.
Qed.

Lemma lookup_zip_with_gen {A : Type} {B C : Type} (f : A -> B -> C)
    (a : list A) (b : list B) (i : nat) :
  zip_with f a b !! i =
  match a !! i, b !! i with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.
Proof.
  revert b i.
  induction a as [|x xs IH]; intros [|y ys] [|i]; simpl; try reflexivity.
  - destruct (xs !! i); reflexivity.
  - apply IH.
Qed.

Lemma zip_with_cmpeq_bounds (a b : list N) :
  List.Forall (fun x => (x < 256)%N) (avx2_cmpeq_epi8 a b).
Proof.
  unfold avx2_cmpeq_epi8.
  revert b.
  induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
  - case_bool_decide; lia.
  - apply IH.
Qed.

Lemma vec256_wf_cmpeq (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_cmpeq_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_cmpeq_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - apply zip_with_cmpeq_bounds.
Qed.

Lemma vec256_wf_add (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_add_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_add_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_add_epi8. clear Hlena Hlenb. revert b.
    induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor;
      [apply N.mod_lt; lia | apply IH].
Qed.

Lemma vec256_wf_sub (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_sub_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_sub_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_sub_epi8.
    clear Hlena Hlenb. revert b.
    induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
    + apply N.mod_lt. lia.
    + apply IH.
Qed.

Lemma vec128_wf_sub (a b : list N) :
  vec128_wf a ->
  vec128_wf b ->
  vec128_wf (sse2_sub_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold sse2_sub_epi8, avx2_sub_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold sse2_sub_epi8, avx2_sub_epi8. clear Hlena Hlenb. revert b.
    induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor;
      [apply N.mod_lt; lia | apply IH].
Qed.

Lemma vec256_wf_cmpgt (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_cmpgt_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_cmpgt_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_cmpgt_epi8.
    clear Hlena Hlenb. revert b.
    induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
    + case_bool_decide; lia.
    + apply IH.
Qed.

#[local] Lemma Forall_max_lt256 (a b : list N) :
  List.Forall (fun x => (x < 256)%N) a ->
  List.Forall (fun x => (x < 256)%N) b ->
  List.Forall (fun x => (x < 256)%N) (zip_with N.max a b).
Proof.
  intros Ha. revert b.
  induction Ha as [|x xs Hx _ IH]; intros [|y ys] Hb; simpl;
    inversion Hb; subst; try constructor; [lia | apply IH; assumption].
Qed.

Lemma vec256_wf_max_epu8 (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_max_epu8 a b).
Proof.
  intros [Hlena Hfa] [Hlenb Hfb].
  split; [unfold avx2_max_epu8; rewrite zip_with_length_gen Hlena Hlenb; reflexivity |].
  exact (Forall_max_lt256 a b Hfa Hfb).
Qed.

Lemma vec128_wf_max_epu8 (a b : list N) :
  vec128_wf a ->
  vec128_wf b ->
  vec128_wf (sse2_max_epu8 a b).
Proof.
  intros [Hlena Hfa] [Hlenb Hfb].
  split; [unfold sse2_max_epu8, avx2_max_epu8; rewrite zip_with_length_gen Hlena Hlenb; reflexivity |].
  exact (Forall_max_lt256 a b Hfa Hfb).
Qed.

Lemma vec256_wf_max_epi8 (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_max_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split; [unfold avx2_max_epi8; rewrite zip_with_length_gen Hlena Hlenb; reflexivity |].
  unfold avx2_max_epi8. clear Hlena Hlenb. revert b.
  induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
  - case_bool_decide; apply N.mod_lt; lia.
  - apply IH.
Qed.

Lemma ssse3_shuffle_epi8_bounds (a mask : list N) :
  List.Forall (fun x => (x < 256)%N) (ssse3_shuffle_epi8 a mask).
Proof.
  unfold ssse3_shuffle_epi8.
  induction mask as [|m rest IH]; simpl; constructor.
  - destruct (N.testbit m 7); [lia | apply N.mod_lt; lia].
  - exact IH.
Qed.

Lemma vec128_wf_shuffle (a mask : list N) :
  vec128_wf a ->
  vec128_wf mask ->
  vec128_wf (ssse3_shuffle_epi8 a mask).
Proof.
  intros _ [Hlenm _].
  split; [unfold ssse3_shuffle_epi8; by rewrite length_fmap | apply ssse3_shuffle_epi8_bounds].
Qed.

Lemma vec256_wf_shuffle (a mask : list N) :
  vec256_wf a ->
  vec256_wf mask ->
  vec256_wf (avx2_shuffle_epi8 a mask).
Proof.
  intros [Hlena _] [Hlenm _].
  split.
  - unfold avx2_shuffle_epi8, ssse3_shuffle_epi8.
    rewrite length_app !length_fmap length_take length_drop Hlenm. lia.
  - unfold avx2_shuffle_epi8.
    apply Forall_app; split; apply ssse3_shuffle_epi8_bounds.
Qed.

Lemma vec256_wf_blendv (v1 v2 mask : list N) :
  vec256_wf v1 ->
  vec256_wf v2 ->
  vec256_wf mask ->
  vec256_wf (avx2_blendv_epi8 v1 v2 mask).
Proof.
  intros [Hlen1 Hf1] [Hlen2 Hf2] [Hlenm _].
  split.
  - unfold avx2_blendv_epi8.
    rewrite zip_with_length_gen zip_with_length_gen Hlen1 Hlen2 Hlenm. lia.
  - unfold avx2_blendv_epi8. clear Hlen1 Hlen2 Hlenm.
    revert v2 mask Hf2.
    induction Hf1 as [|x xs Hx _ IH]; intros [|y ys] [|m ms] Hf2; simpl;
      try constructor; inversion Hf2; subst.
    + destruct (N.testbit m 7); assumption.
    + apply IH; assumption.
Qed.

Lemma N_bitwise_lt_256 (op : N -> N -> N) (x y : N) :
  (forall k, N.testbit (op x y) k = true -> N.testbit x k = true \/ N.testbit y k = true) ->
  (x < 256)%N ->
  (y < 256)%N ->
  (op x y < 256)%N.
Proof.
  change 256%N with (2 ^ 8)%N.
  intros Hop Hx Hy.
  destruct (N.eq_dec (op x y) 0%N) as [-> | Hnz]; [lia |].
  apply N.log2_lt_pow2; [lia |].
  set (k := N.log2 (op x y)).
  destruct (N.lt_ge_cases k 8) as [Hk | Hge8]; [exact Hk |].
  have Hbit : N.testbit (op x y) k = true by (subst k; apply N.bit_log2).
  destruct (Hop k Hbit) as [Hbx | Hby].
  - destruct (N.eq_dec x 0%N) as [-> | Hx0]; [by destruct k |].
    have Hlt : (N.log2 x < 8)%N by apply N.log2_lt_pow2; lia.
    by rewrite (N.bits_above_log2 x k ltac:(lia)) in Hbx.
  - destruct (N.eq_dec y 0%N) as [-> | Hy0]; [by destruct k |].
    have Hlt : (N.log2 y < 8)%N by apply N.log2_lt_pow2; lia.
    by rewrite (N.bits_above_log2 y k ltac:(lia)) in Hby.
Qed.

Lemma N_lor_lt_256 (x y : N) :
  (x < 256)%N ->
  (y < 256)%N ->
  (N.lor x y < 256)%N.
Proof.
  apply N_bitwise_lt_256.
  intros k. rewrite N.lor_spec Bool.orb_true_iff. tauto.
Qed.

Lemma vec256_wf_and (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_and_si256 a b).
Proof.
  intros [Hlena Hfa] [Hlenb Hfb].
  split; [unfold avx2_and_si256; rewrite zip_with_length_gen Hlena Hlenb; reflexivity |].
  unfold avx2_and_si256. clear Hlena Hlenb. revert b Hfb.
  induction Hfa as [|x xs Hx _ IH]; intros [|y ys] Hfb; simpl;
    inversion Hfb; subst; try constructor.
  - apply (N_bitwise_lt_256 N.land x y); [| exact Hx | assumption].
    intros k. rewrite N.land_spec Bool.andb_true_iff. tauto.
  - apply IH; assumption.
Qed.

Lemma vec256_wf_or (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_or_si256 a b).
Proof.
  intros [Hlena Hfa] [Hlenb Hfb].
  split.
  - unfold avx2_or_si256. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_or_si256.
    clear Hlena Hlenb. revert b Hfb.
    induction Hfa as [|x xs Hx _ IH]; intros [|y ys] Hfb; simpl;
      inversion Hfb; subst; try constructor.
    + apply N_lor_lt_256; assumption.
    + apply IH; assumption.
Qed.

Lemma vec256_wf_xor (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_xor_si256 a b).
Proof.
  intros [Hlena Hfa] [Hlenb Hfb].
  split; [unfold avx2_xor_si256; rewrite zip_with_length_gen Hlena Hlenb; reflexivity |].
  unfold avx2_xor_si256. clear Hlena Hlenb. revert b Hfb.
  induction Hfa as [|x xs Hx _ IH]; intros [|y ys] Hfb; simpl;
    inversion Hfb; subst; try constructor.
  - apply (N_bitwise_lt_256 N.lxor x y); [| exact Hx | assumption].
    intros k. rewrite N.lxor_spec.
    destruct (N.testbit x k), (N.testbit y k); simpl; intuition congruence.
  - apply IH; assumption.
Qed.

Lemma vec128_wf_castsi256_si128 (v : list N) :
  vec256_wf v ->
  vec128_wf (avx2_castsi256_si128 v).
Proof.
  intros [Hlen Hfv].
  split; [unfold avx2_castsi256_si128; rewrite length_take Hlen; lia |].
  exact (Forall_take_gen _ 16 v Hfv).
Qed.

Lemma vec128_wf_extracti128_si256 (v : list N) (imm : Z) :
  vec256_wf v ->
  vec128_wf (avx2_extracti128_si256 v imm).
Proof.
  intros [Hlen Hfv].
  unfold avx2_extracti128_si256.
  case_bool_decide.
  - split; [rewrite length_take length_drop Hlen; lia |].
    apply Forall_take_gen, Forall_drop_gen; exact Hfv.
  - split; [rewrite length_take Hlen; lia |].
    exact (Forall_take_gen _ 16 v Hfv).
Qed.

Lemma vec256_wf_set_m128i (hi lo : list N) :
  vec128_wf hi ->
  vec128_wf lo ->
  vec256_wf (avx2_set_m128i hi lo).
Proof.
  intros [Hlenhi Hfhi] [Hlenlo Hflo].
  split.
  - unfold avx2_set_m128i. rewrite length_app Hlenlo Hlenhi. reflexivity.
  - unfold avx2_set_m128i. apply Forall_app; split; assumption.
Qed.

Lemma movemask_bytes_bound (bs : list N) :
  (movemask_bytes bs < 2 ^ N.of_nat (length bs))%N.
Proof.
  induction bs as [|b rest IH]; simpl.
  - lia.
  - rewrite Nat2N.inj_succ N.pow_succ_r'.
    destruct (N.testbit b 7); lia.
Qed.

Lemma avx2_movemask_epi8_bound (bs : list N) :
  vec256_wf bs ->
  (avx2_movemask_epi8 bs < 2 ^ 32)%N.
Proof.
  intros [Hlen _].
  unfold avx2_movemask_epi8.
  pose proof (movemask_bytes_bound bs) as Hbound.
  rewrite Hlen in Hbound.
  exact Hbound.
Qed.

Lemma avx2_movemask_epi8_testbit (bs : list N) (i : nat) :
  N.testbit (avx2_movemask_epi8 bs) (N.of_nat i) =
  match bs !! i with
  | Some b => N.testbit b 7
  | None => false
  end.
Proof.
  unfold avx2_movemask_epi8.
  revert i.
  induction bs as [|b rest IH]; intros [|i]; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (N.testbit b 7).
    + apply N.testbit_odd_0.
    + apply N.testbit_even_0.
  - rewrite Nat2N.inj_succ.
    destruct (N.testbit b 7).
    + rewrite N.testbit_odd_succ; [apply IH | lia].
    + rewrite N.testbit_even_succ; [apply IH | lia].
Qed.

Lemma lookup_repeat_lt {A : Type} (x : A) (n i : nat) :
  (i < n)%nat ->
  repeat x n !! i = Some x.
Proof.
  revert i.
  induction n as [|n IH]; intros [|i] Hi; simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

(** Per-lane lookup for [ssse3_shuffle_epi8] and [avx2_shuffle_epi8]. *)
Lemma ssse3_shuffle_epi8_lookup (a mask : list N) (i : nat) :
  vec128_wf a ->
  (i < 16)%nat ->
  ssse3_shuffle_epi8 a mask !! i =
  (fun m =>
     if N.testbit m 7
     then 0%N
     else default 0%N (a !! N.to_nat (m mod 16))) <$> (mask !! i).
Proof.
  intros [_ Hfa] _.
  unfold ssse3_shuffle_epi8.
  rewrite list_lookup_fmap.
  destruct (mask !! i) as [m|]; simpl; [| reflexivity].
  f_equal.
  destruct (N.testbit m 7); [reflexivity |].
  destruct (a !! N.to_nat (m mod 16)) as [v|] eqn:Hv; simpl.
  - rewrite N.mod_small; [reflexivity |].
    exact (Forall_lookup_1 _ _ _ _ Hfa Hv).
  - reflexivity.
Qed.

Lemma avx2_shuffle_epi8_lookup (a mask : list N) (i : nat) :
  vec256_wf a ->
  vec256_wf mask ->
  (i < 32)%nat ->
  avx2_shuffle_epi8 a mask !! i =
  let base := if bool_decide (i < 16)%nat then 0%nat else 16%nat in
  (fun m =>
     if N.testbit m 7
     then 0%N
     else default 0%N (a !! (base + N.to_nat (m mod 16))%nat)) <$> (mask !! i).
Proof.
  intros [Hlena Hfa] [Hlenm Hfm] Hi.
  unfold avx2_shuffle_epi8.
  have Hlen_lo : length (ssse3_shuffle_epi8 (take 16 a) (take 16 mask)) = 16%nat.
  { unfold ssse3_shuffle_epi8. rewrite length_fmap length_take Hlenm. lia. }
  have Hwf_lo : vec128_wf (take 16 a).
  { split; [rewrite length_take Hlena; lia | exact (Forall_take_gen _ 16 a Hfa)]. }
  have Hwf_hi : vec128_wf (drop 16 a).
  { split; [rewrite length_drop Hlena; lia | exact (Forall_drop_gen _ 16 a Hfa)]. }
  have Hmod16 : forall m : N, (N.to_nat (m mod 16) < 16)%nat.
  { intros m. pose proof (N.mod_lt m 16 ltac:(lia)). lia. }
  case_bool_decide as Hlt16; simpl.
  - rewrite lookup_app_l; [| lia].
    rewrite (ssse3_shuffle_epi8_lookup (take 16 a) (take 16 mask) i Hwf_lo Hlt16).
    rewrite lookup_take_lt; [| lia].
    destruct (mask !! i) as [m|]; simpl; [| reflexivity].
    rewrite lookup_take_lt; [reflexivity | apply Hmod16].
  - rewrite lookup_app_r; [| lia].
    rewrite Hlen_lo.
    rewrite (ssse3_shuffle_epi8_lookup (drop 16 a) (drop 16 mask) (i - 16)%nat Hwf_hi ltac:(lia)).
    rewrite lookup_drop.
    replace (16 + (i - 16))%nat with i by lia.
    destruct (mask !! i) as [m|]; simpl; [| reflexivity].
    rewrite lookup_drop. reflexivity.
Qed.

Lemma avx2_blendv_epi8_lookup (v1 v2 mask : list N) (i : nat) :
  avx2_blendv_epi8 v1 v2 mask !! i =
  match v1 !! i, v2 !! i, mask !! i with
  | Some x, Some y, Some m => Some (if N.testbit m 7 then y else x)
  | _, _, _ => None
  end.
Proof.
  unfold avx2_blendv_epi8, zip.
  rewrite !lookup_zip_with_gen.
  destruct (v1 !! i), (v2 !! i), (mask !! i); reflexivity.
Qed.

(** Bit-level equivalence of [_mm256_cmpeq_epi8] + [_mm256_movemask_epi8]. *)
Theorem avx2_cmpeq_movemask_bit_spec (bs : list N) (needle : N) (i : nat) :
  vec256_wf bs ->
  (needle < 256)%N ->
  (i < 32)%nat ->
  N.testbit (avx2_movemask_epi8 (avx2_cmpeq_epi8 bs (avx2_set1_epi8 needle))) (N.of_nat i) =
  bool_decide (bs !! i = Some needle).
Proof.
  intros [Hlen _] Hneedle Hi.
  rewrite avx2_movemask_epi8_testbit /avx2_cmpeq_epi8 lookup_zip_with_gen.
  rewrite (avx2_set1_epi8_small needle Hneedle).
  rewrite (lookup_repeat_lt needle 32 i Hi).
  destruct (lookup_lt_is_Some_2 bs i ltac:(lia)) as [b Hb].
  rewrite Hb.
  case_bool_decide as Heq.
  - subst b. rewrite bool_decide_eq_true_2; [reflexivity | reflexivity].
  - rewrite bool_decide_eq_false_2; [reflexivity | congruence].
Qed.

(** Unsigned byte range test [0x60 <= b <= 0x7f] via signed-byte bias trick
    (used with [_mm256_sub_epi8] and [_mm256_cmpgt_epi8]). *)
Lemma avx2_signed_bias_range_0x60_0x7f (b : N) :
  (b < 256)%N ->
  bool_decide
    (sbyte_of_N (0xa0 mod 256) >
     sbyte_of_N (((b + 256 - 0xe0 mod 256) mod 256) mod 256))%Z =
  bool_decide (0x60 <= b <= 0x7f)%N.
Proof.
  intros Hb.
  change (0xa0 mod 256)%N with 160%N.
  change (0xe0 mod 256)%N with 224%N.
  rewrite N.Div0.mod_mod.
  replace (sbyte_of_N 160) with (-96)%Z by reflexivity.
  destruct (N.lt_ge_cases b 224) as [Hlt224 | Hge224].
  - replace (b + 256 - 224)%N with (b + 32)%N by lia.
    rewrite (N.mod_small (b + 32)%N 256%N ltac:(lia)).
    unfold sbyte_of_N.
    repeat case_bool_decide; try reflexivity; lia.
  - replace (b + 256 - 224)%N with ((b - 224) + 1 * 256)%N by lia.
    rewrite N.Div0.mod_add.
    rewrite (N.mod_small (b - 224)%N 256%N ltac:(lia)).
    unfold sbyte_of_N.
    repeat case_bool_decide; try reflexivity; lia.
Qed.

Succeed Example ex_movemask_set1_high :
  avx2_movemask_epi8 (avx2_set1_epi8 0x80) = 0xffffffff%N := eq_refl.
Succeed Example ex_movemask_set1_low :
  avx2_movemask_epi8 (avx2_set1_epi8 0x7f) = 0%N := eq_refl.
