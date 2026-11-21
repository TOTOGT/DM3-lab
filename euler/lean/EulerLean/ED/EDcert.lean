import EDcertCore
import EDcertC1
import EDcertD0
import EDcertD1
import EDcertD2
import EDcertD3
import EDcertD4
import EDcertD5
import EDcertD6
import EDcertD7
import EDcertD8
import EDcertD9
import EDcertD10
import EDcertD11
import EDcertD12
import EDcertD13

namespace EDcert
open Euler1747

theorem chunks_ok (c : ℕ) (hc : c < 256) : chunkOk c = true := by
  interval_cases c
  exacts [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28, chunk_29, chunk_30, chunk_31, chunk_32, chunk_33, chunk_34, chunk_35, chunk_36, chunk_37, chunk_38, chunk_39, chunk_40, chunk_41, chunk_42, chunk_43, chunk_44, chunk_45, chunk_46, chunk_47, chunk_48, chunk_49, chunk_50, chunk_51, chunk_52, chunk_53, chunk_54, chunk_55, chunk_56, chunk_57, chunk_58, chunk_59, chunk_60, chunk_61, chunk_62, chunk_63, chunk_64, chunk_65, chunk_66, chunk_67, chunk_68, chunk_69, chunk_70, chunk_71, chunk_72, chunk_73, chunk_74, chunk_75, chunk_76, chunk_77, chunk_78, chunk_79, chunk_80, chunk_81, chunk_82, chunk_83, chunk_84, chunk_85, chunk_86, chunk_87, chunk_88, chunk_89, chunk_90, chunk_91, chunk_92, chunk_93, chunk_94, chunk_95, chunk_96, chunk_97, chunk_98, chunk_99, chunk_100, chunk_101, chunk_102, chunk_103, chunk_104, chunk_105, chunk_106, chunk_107, chunk_108, chunk_109, chunk_110, chunk_111, chunk_112, chunk_113, chunk_114, chunk_115, chunk_116, chunk_117, chunk_118, chunk_119, chunk_120, chunk_121, chunk_122, chunk_123, chunk_124, chunk_125, chunk_126, chunk_127, chunk_128, chunk_129, chunk_130, chunk_131, chunk_132, chunk_133, chunk_134, chunk_135, chunk_136, chunk_137, chunk_138, chunk_139, chunk_140, chunk_141, chunk_142, chunk_143, chunk_144, chunk_145, chunk_146, chunk_147, chunk_148, chunk_149, chunk_150, chunk_151, chunk_152, chunk_153, chunk_154, chunk_155, chunk_156, chunk_157, chunk_158, chunk_159, chunk_160, chunk_161, chunk_162, chunk_163, chunk_164, chunk_165, chunk_166, chunk_167, chunk_168, chunk_169, chunk_170, chunk_171, chunk_172, chunk_173, chunk_174, chunk_175, chunk_176, chunk_177, chunk_178, chunk_179, chunk_180, chunk_181, chunk_182, chunk_183, chunk_184, chunk_185, chunk_186, chunk_187, chunk_188, chunk_189, chunk_190, chunk_191, chunk_192, chunk_193, chunk_194, chunk_195, chunk_196, chunk_197, chunk_198, chunk_199, chunk_200, chunk_201, chunk_202, chunk_203, chunk_204, chunk_205, chunk_206, chunk_207, chunk_208, chunk_209, chunk_210, chunk_211, chunk_212, chunk_213, chunk_214, chunk_215, chunk_216, chunk_217, chunk_218, chunk_219, chunk_220, chunk_221, chunk_222, chunk_223, chunk_224, chunk_225, chunk_226, chunk_227, chunk_228, chunk_229, chunk_230, chunk_231, chunk_232, chunk_233, chunk_234, chunk_235, chunk_236, chunk_237, chunk_238, chunk_239, chunk_240, chunk_241, chunk_242, chunk_243, chunk_244, chunk_245, chunk_246, chunk_247, chunk_248, chunk_249, chunk_250, chunk_251, chunk_252, chunk_253, chunk_254, chunk_255]

theorem euler_finite_k (n : ℕ) (hn : n % 4 = 2) (hlt : n < 64 ^ 4) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n ∧ min a b ≤ 313 := by
  have h64 : (64 : ℕ) ^ 4 = 16777216 := by norm_num
  rw [h64] at hlt
  have hc : n / W < 256 := by unfold W; omega
  obtain ⟨a, han, ha313, hag, hgood⟩ := chunk_sound (n / W) (chunks_ok _ hc) n
    (by unfold W; omega) (by unfold W; omega) hn
  exact ⟨a, n - a, hag, hgood, by omega, le_trans (min_le_left _ _) ha313⟩

/-- Copy of `Euler1747.euler_1747_of_analytic_range` with the finite range supplied by `euler_finite_k`. -/
theorem euler_1747_of_analytic_range_k (H : AnalyticRange) (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n := by
  obtain ⟨m, rfl, hm⟩ : ∃ m, n = 2 * m ∧ m % 2 = 1 := ⟨n / 2, by omega, by omega⟩
  clear hn
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hex : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 1
    · obtain ⟨p, hp, hpd, hp1⟩ := hex
      obtain ⟨m', rfl⟩ := hpd
      have hm' : m' % 2 = 1 :=
        Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hm)).2
      have hp2 := hp.two_le
      have hm'pos : 0 < m' := by omega
      have hlt : m' < p * m' := by nlinarith
      obtain ⟨a, b, ha, hb, hab⟩ := ih m' hlt hm'
      have hpg : EulerGood p :=
        ⟨hp.pos, fun q hq hqd => by rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 hqd]; exact hp1⟩
      exact ⟨p * a, p * b, good_mul hpg ha, good_mul hpg hb, by rw [← mul_add, hab]; ring⟩
    · have h3 : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3 := by
        intro p hp hpd
        rcases hp.eq_two_or_odd with h2 | h2
        · subst h2; omega
        · have : p % 4 ≠ 1 := fun h1 => hex ⟨p, hp, hpd, h1⟩
          omega
      by_cases hbig : 64 ^ 4 ≤ 2 * m
      · exact H m hm h3 hbig
      · obtain ⟨a, b, ha, hb, hab, -⟩ := euler_finite_k (2 * m) (by omega) (not_le.1 hbig)
        exact ⟨a, b, ha, hb, hab⟩

/-- Same statement as `Section83.euler_1747_of_H31gt3`, with the finite range checked in the kernel. -/
theorem euler_1747_of_H31gt3_k (h : Section83.H31gt3) (n : ℕ) (hn4 : n % 4 = 2) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n :=
  euler_1747_of_analytic_range_k
    (Section65.analytic_range_of Section65.hr2
      (Section70.h31_of_ndvd (Section83.h31ndvd_of h) Section81.hjac) Section81.hjac) n hn4

end EDcert
#print axioms EDcert.good_of_sq_add_sq
#print axioms EDcert.chunk_sound
#print axioms EDcert.euler_finite_k
#print axioms EDcert.euler_1747_of_H31gt3_k
