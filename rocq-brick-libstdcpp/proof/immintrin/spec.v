(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.immintrin.model.
Require Export skylabs.brick.libstdcpp.immintrin.pred.
Require Import skylabs.brick.libstdcpp.immintrin.inc_immintrin_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** Assumed specifications for 128-bit SSE2/SSSE3 and 256-bit AVX2 intrinsics in [<immintrin.h>]. *)

  cpp.spec "_mm256_loadu_si256(const __m256i_u *)" as mm256_loadu_si256_spec with (
    \arg{p : ptr} "__p" (Vptr p)
    \prepost{(q : cQp.t) (bs : list N)}
      p |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs)
    \require vec256_wf bs
    \post[Vvec bs] emp).

  cpp.spec "_mm256_storeu_si256(__m256i_u *, __m256i)" as mm256_storeu_si256_spec with (
    \arg{p : ptr} "__p" (Vptr p)
    \arg{v : list N} "__a" (Vvec v)
    \pre p |-> arrayR Tuchar (fun _ : unit => anyR Tuchar 1$m) (repeat tt 32%nat)
    \require vec256_wf v
    \post p |-> arrayR Tuchar (primR Tuchar 1$m) (Vn <$> v)).

  cpp.spec "_mm256_setzero_si256()" as mm256_setzero_si256_spec with (
    \post[Vvec avx2_setzero_si256] emp).

  cpp.spec "_mm_set1_epi8(char)" as mm_set1_epi8_spec with (
    \arg{b : N} "__b" (Vchar b)
    \require (b < 256)%N
    \post[Vvec (sse2_set1_epi8 b)] emp).

  cpp.spec "_mm256_set1_epi8(char)" as mm256_set1_epi8_spec with (
    \arg{b : N} "__b" (Vchar b)
    \require (b < 256)%N
    \post[Vvec (avx2_set1_epi8 b)] emp).

  cpp.spec "_mm256_setr_epi8(char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char, char)" as mm256_setr_epi8_spec with (
    \arg{e0 : N} "__b31" (Vchar e0)
    \arg{e1 : N} "__b30" (Vchar e1)
    \arg{e2 : N} "__b29" (Vchar e2)
    \arg{e3 : N} "__b28" (Vchar e3)
    \arg{e4 : N} "__b27" (Vchar e4)
    \arg{e5 : N} "__b26" (Vchar e5)
    \arg{e6 : N} "__b25" (Vchar e6)
    \arg{e7 : N} "__b24" (Vchar e7)
    \arg{e8 : N} "__b23" (Vchar e8)
    \arg{e9 : N} "__b22" (Vchar e9)
    \arg{e10 : N} "__b21" (Vchar e10)
    \arg{e11 : N} "__b20" (Vchar e11)
    \arg{e12 : N} "__b19" (Vchar e12)
    \arg{e13 : N} "__b18" (Vchar e13)
    \arg{e14 : N} "__b17" (Vchar e14)
    \arg{e15 : N} "__b16" (Vchar e15)
    \arg{e16 : N} "__b15" (Vchar e16)
    \arg{e17 : N} "__b14" (Vchar e17)
    \arg{e18 : N} "__b13" (Vchar e18)
    \arg{e19 : N} "__b12" (Vchar e19)
    \arg{e20 : N} "__b11" (Vchar e20)
    \arg{e21 : N} "__b10" (Vchar e21)
    \arg{e22 : N} "__b09" (Vchar e22)
    \arg{e23 : N} "__b08" (Vchar e23)
    \arg{e24 : N} "__b07" (Vchar e24)
    \arg{e25 : N} "__b06" (Vchar e25)
    \arg{e26 : N} "__b05" (Vchar e26)
    \arg{e27 : N} "__b04" (Vchar e27)
    \arg{e28 : N} "__b03" (Vchar e28)
    \arg{e29 : N} "__b02" (Vchar e29)
    \arg{e30 : N} "__b01" (Vchar e30)
    \arg{e31 : N} "__b00" (Vchar e31)
    \require (e0 < 256)%N
    \require (e1 < 256)%N
    \require (e2 < 256)%N
    \require (e3 < 256)%N
    \require (e4 < 256)%N
    \require (e5 < 256)%N
    \require (e6 < 256)%N
    \require (e7 < 256)%N
    \require (e8 < 256)%N
    \require (e9 < 256)%N
    \require (e10 < 256)%N
    \require (e11 < 256)%N
    \require (e12 < 256)%N
    \require (e13 < 256)%N
    \require (e14 < 256)%N
    \require (e15 < 256)%N
    \require (e16 < 256)%N
    \require (e17 < 256)%N
    \require (e18 < 256)%N
    \require (e19 < 256)%N
    \require (e20 < 256)%N
    \require (e21 < 256)%N
    \require (e22 < 256)%N
    \require (e23 < 256)%N
    \require (e24 < 256)%N
    \require (e25 < 256)%N
    \require (e26 < 256)%N
    \require (e27 < 256)%N
    \require (e28 < 256)%N
    \require (e29 < 256)%N
    \require (e30 < 256)%N
    \require (e31 < 256)%N
    \post[Vvec (avx2_setr_epi8 [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15; e16; e17; e18; e19; e20; e21; e22; e23; e24; e25; e26; e27; e28; e29; e30; e31])] emp).

  cpp.spec "_mm256_cmpeq_epi8(__m256i, __m256i)" as mm256_cmpeq_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_cmpeq_epi8 a b)] emp).

  cpp.spec "_mm256_add_epi8(__m256i, __m256i)" as mm256_add_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_add_epi8 a b)] emp).

  cpp.spec "_mm256_sub_epi8(__m256i, __m256i)" as mm256_sub_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_sub_epi8 a b)] emp).

  cpp.spec "_mm_sub_epi8(__m128i, __m128i)" as mm_sub_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec128_wf a
    \require vec128_wf b
    \post[Vvec (sse2_sub_epi8 a b)] emp).

  cpp.spec "_mm256_cmpgt_epi8(__m256i, __m256i)" as mm256_cmpgt_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_cmpgt_epi8 a b)] emp).

  cpp.spec "_mm256_max_epu8(__m256i, __m256i)" as mm256_max_epu8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_max_epu8 a b)] emp).

  cpp.spec "_mm_max_epu8(__m128i, __m128i)" as mm_max_epu8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec128_wf a
    \require vec128_wf b
    \post[Vvec (sse2_max_epu8 a b)] emp).

  cpp.spec "_mm256_max_epi8(__m256i, __m256i)" as mm256_max_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_max_epi8 a b)] emp).

  cpp.spec "_mm256_shuffle_epi8(__m256i, __m256i)" as mm256_shuffle_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_shuffle_epi8 a b)] emp).

  cpp.spec "_mm_shuffle_epi8(__m128i, __m128i)" as mm_shuffle_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec128_wf a
    \require vec128_wf b
    \post[Vvec (ssse3_shuffle_epi8 a b)] emp).

  cpp.spec "_mm256_blendv_epi8(__m256i, __m256i, __m256i)" as mm256_blendv_epi8_spec with (
    \arg{v1 : list N} "__V1" (Vvec v1)
    \arg{v2 : list N} "__V2" (Vvec v2)
    \arg{mask : list N} "__M" (Vvec mask)
    \require vec256_wf v1
    \require vec256_wf v2
    \require vec256_wf mask
    \post[Vvec (avx2_blendv_epi8 v1 v2 mask)] emp).

  cpp.spec "_mm256_and_si256(__m256i, __m256i)" as mm256_and_si256_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_and_si256 a b)] emp).

  cpp.spec "_mm256_or_si256(__m256i, __m256i)" as mm256_or_si256_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_or_si256 a b)] emp).

  cpp.spec "_mm256_xor_si256(__m256i, __m256i)" as mm256_xor_si256_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_xor_si256 a b)] emp).

  cpp.spec "_mm256_castsi256_si128(__m256i)" as mm256_castsi256_si128_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \require vec256_wf a
    \post[Vvec (avx2_castsi256_si128 a)] emp).

  cpp.spec "_mm256_set_m128i(__m128i, __m128i)" as mm256_set_m128i_spec with (
    \arg{hi : list N} "__hi" (Vvec hi)
    \arg{lo : list N} "__lo" (Vvec lo)
    \require vec128_wf hi
    \require vec128_wf lo
    \post[Vvec (avx2_set_m128i hi lo)] emp).

  cpp.spec "_mm256_movemask_epi8(__m256i)" as mm256_movemask_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \require vec256_wf a
    \post[Vint (to_signed bitsize.W32 (Z.of_N (avx2_movemask_epi8 a)))] emp).

End with_cpp.

(** [_mm256_extracti128_si256(v, imm)] expands as a macro to the compiler builtin
    [__builtin_ia32_extract128i256]. *)
Section with_extract_builtin.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition builtin_ia32_extract128i256_spec : mpred :=
    specify.exact.func (Nglobal (Nid "__builtin_ia32_extract128i256"))
      Tm128i [Tm256i; Tint] (
      \arg{v : list N} "v" (Vvec v)
      \arg{imm : Z} "imm" (Vint imm)
      \require vec256_wf v
      \post[Vvec (avx2_extracti128_si256 v imm)] emp).
  #[global] Hint Opaque builtin_ia32_extract128i256_spec : sl_opacity.
  #[global] Arguments builtin_ia32_extract128i256_spec : simpl never.
  Definition SpecFor_builtin_ia32_extract128i256 :=
    RegisterSpec builtin_ia32_extract128i256_spec.
  #[global] Existing Instance SpecFor_builtin_ia32_extract128i256.
End with_extract_builtin.
