Require Import NZAxioms.
Require Import NZPlus.

Module NZTimesPropFunct (Import NZAxiomsMod : NZAxiomsSig).
Module Export NZPlusPropMod := NZPlusPropFunct NZAxiomsMod.
Open Local Scope NatIntScope.

Theorem NZtimes_0_l : forall n : NZ, 0 * n == 0.
Proof.
NZinduct n.
now rewrite NZtimes_0_r.
intro. rewrite NZtimes_succ_r. now rewrite NZplus_0_r.
Qed.

Theorem NZtimes_succ_l : forall n m : NZ, (S n) * m == n * m + m.
Proof.
intros n m; NZinduct m.
do 2 rewrite NZtimes_0_r; now rewrite NZplus_0_l.
intro m. do 2 rewrite NZtimes_succ_r. do 2 rewrite NZplus_succ_r.
rewrite NZsucc_inj_wd. rewrite <- (NZplus_assoc (n * m) n m).
rewrite (NZplus_comm n m). rewrite NZplus_assoc.
now rewrite NZplus_cancel_r.
Qed.

Theorem NZtimes_comm : forall n m : NZ, n * m == m * n.
Proof.
intros n m; NZinduct n.
rewrite NZtimes_0_l; now rewrite NZtimes_0_r.
intro. rewrite NZtimes_succ_l; rewrite NZtimes_succ_r. now rewrite NZplus_cancel_r.
Qed.

Theorem NZtimes_plus_distr_r : forall n m p : NZ, (n + m) * p == n * p + m * p.
Proof.
intros n m p; NZinduct n.
rewrite NZtimes_0_l. now do 2 rewrite NZplus_0_l.
intro n. rewrite NZplus_succ_l. do 2 rewrite NZtimes_succ_l.
rewrite <- (NZplus_assoc (n * p) p (m * p)).
rewrite (NZplus_comm p (m * p)). rewrite (NZplus_assoc (n * p) (m * p) p).
now rewrite NZplus_cancel_r.
Qed.

Theorem NZtimes_plus_distr_l : forall n m p : NZ, n * (m + p) == n * m + n * p.
Proof.
intros n m p.
rewrite (NZtimes_comm n (m + p)). rewrite (NZtimes_comm n m).
rewrite (NZtimes_comm n p). apply NZtimes_plus_distr_r.
Qed.

Theorem NZtimes_assoc : forall n m p : NZ, n * (m * p) == (n * m) * p.
Proof.
intros n m p; NZinduct n.
now do 3 rewrite NZtimes_0_l.
intro n. do 2 rewrite NZtimes_succ_l. rewrite NZtimes_plus_distr_r.
now rewrite NZplus_cancel_r.
Qed.

Theorem NZtimes_1_l : forall n : NZ, 1 * n == n.
Proof.
intro n. rewrite NZtimes_succ_l; rewrite NZtimes_0_l. now rewrite NZplus_0_l.
Qed.

Theorem NZtimes_1_r : forall n : NZ, n * 1 == n.
Proof.
intro n; rewrite NZtimes_comm; apply NZtimes_1_l.
Qed.

End NZTimesPropFunct.

