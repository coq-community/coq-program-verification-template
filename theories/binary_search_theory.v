(* This file contains code adapted from the VST project.

Copyright (c) 2007-2018 by Andrew W. Appel,
Lennart Beringer, Robert Dockins, Josiah Dodds, Aquinas Hobor,
Gordon Stewart, and Qinxiang Cao, and others,
and open-source licensed as follows:

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

- Redistribution of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.

- Redistribution in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation
and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS "AS IS" AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR THE CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

From VST Require Import floyd.proofauto floyd.sublist.

Fixpoint sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x::rest =>
    match rest with [] => True | y::_ =>  x <= y /\ sorted rest end
  end.

Definition insertion_point (ip : Z)  (l : list Z) (key : Z) : Prop :=
0 <= ip <= Zlength l /\
Forall (fun x => x < key) (sublist 0 ip l) /\
Forall (fun x => key < x) (sublist ip (Zlength l) l).

Lemma sublist_nil1 : forall A i j (l : list A), j <= i -> sublist i j l = [].
Proof.
  intros *.
  apply sublist_nil_gen.
Qed.

Lemma Znth_In : forall A (d: Inhabitant A) i (l : list A) x (Hrange : 0 <= i < Zlength l)
 (Hnth : Znth i l = x), In x l.
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); [lia|].
  subst; apply nth_In.
  rewrite Zlength_correct in Hrange; auto.
  rep_lia.
Qed.

Lemma In_Znth : forall A (d: Inhabitant A) (l : list A) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  unfold Znth; intros.
  apply In_nth with (d := d) in H; destruct H as (n & ? & ?).
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; lia.
  - destruct (zlt (Z.of_nat n) 0); [lia|].
    rewrite Nat2Z.id; auto.
Qed.

Lemma sublist_of_nil : forall A i j, sublist i j (nil : list A) = [].
Proof.
  intros; unfold sublist.
  rewrite firstn_nil, skipn_nil; auto.
Qed.

Fixpoint sorted2 l :=
  match l with
  | [] => True
  | x :: rest => Forall (fun y => x <= y) rest /\ sorted2 rest
  end.

Lemma sorted_equiv : forall l, sorted l <-> sorted2 l.
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct l.
    + simpl; split; auto.
    + rewrite IHl; simpl; split; intros (? & Hall & ?); split3; auto.
       * constructor; auto.
          rewrite Forall_forall in *; intros ? Hin.
          specialize (Hall _ Hin); lia.
       * inversion H. auto.
Qed.

Lemma sorted_mono : forall l i j (Hsort : sorted l) (Hi : 0 <= i <= j)
                           (Hj : j < Zlength l),
    Znth i l <= Znth j l.
Proof.
induction l; intros.
* rewrite !Znth_nil. lia.
* 
 rewrite sorted_equiv in Hsort. destruct Hsort as [H9 Hsort].
 rewrite <- sorted_equiv in Hsort. rewrite Forall_forall in H9.
 rewrite Zlength_cons in Hj.
 destruct (zeq i 0).
 +
   subst i; rewrite Znth_0_cons. 
   destruct (zeq j 0).
   - subst j. rewrite Znth_0_cons. lia.
   - rewrite Znth_pos_cons by lia.
      apply H9.
      eapply Znth_In; [ | reflexivity]; lia.
 +
    rewrite !Znth_pos_cons by lia.
    apply IHl; auto; lia.
Qed.

Lemma In_sorted_range : forall lo hi x l (Hsort : sorted l) (Hlo : 0 <= lo <= hi)
                              (Hhi : hi <= Zlength l)
                              (Hin : In x (sublist lo hi l)),
    Znth lo l <= x <= Znth (hi - 1) l.
Proof.
  intros.
  generalize (In_Znth _ _ _ _ Hin); intros (i & Hrange & Hi).
  rewrite Zlength_sublist in Hrange by auto.
  rewrite Znth_sublist in Hi by lia.
  subst; split; apply sorted_mono; auto; lia.
Qed.

Lemma In_sorted_gt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l = n)
                            (Hgt : n < x),
    In x (sublist (i + 1) hi l).
Proof.
  intros.
  rewrite sublist_split with (mid := i + 1) in Hin; try lia.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range lo (i + 1) x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | lia]).
  replace (i + 1 - 1) with i in X by lia.
  specialize (X H); subst; lia.
Qed.

Lemma In_sorted_lt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l = n)
                            (Hgt : x < n),
    In x (sublist lo i l).
Proof.
  intros.
  rewrite sublist_split with (mid := i) in Hin; try lia.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range i hi x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | lia]).
  specialize (X H); subst; lia.
Qed.

Lemma Znth_In_sublist : forall A (d: Inhabitant A) i (l : list A) lo hi
  (Hlo : 0 <= lo <= i) (Hhi : i < hi <= Zlength l),
  In (Znth i l) (sublist lo hi l).
Proof.
  intros.
  apply Znth_In with (i := i - lo)(d := d).
  - rewrite Zlength_sublist; lia.
  - rewrite <- (Z.sub_simpl_r i lo) at 2.
    apply Znth_sublist; lia.
Qed.

Lemma sublist_In_sublist : forall A (l : list A) x lo hi lo' hi' (Hlo : 0 <= lo <= lo')
  (Hhi : hi' <= hi), In x (sublist lo' hi' l) -> In x (sublist lo hi l).
Proof.
  intros.
  apply sublist_In with (lo0 := lo' - lo)(hi0 := hi' - lo); rewrite sublist_sublist;
    try split; try lia.
  - repeat rewrite Z.sub_simpl_r; auto.
  - destruct (Z_le_dec hi' lo'); try lia.
    rewrite sublist_nil1 in *; auto; simpl in *; contradiction.
Qed.

Lemma mean_le_plus : forall i j : Z,
 i <= j ->
 i <= (i + j)/2 <= j.
Proof.
intros.
split.
- apply Zdiv_le_lower_bound; lia.
- apply Zdiv_le_upper_bound; lia.
Qed.

Lemma Znth_lt_sublist_lt :
  forall l i x key,
    0 <= i < Zlength l ->
    sorted l ->
    Znth i l < key ->
    In x (sublist 0 (i + 1) l) ->
    x < key.
Proof.
intros.
apply (In_sorted_range _ _ _ _ H0) in H2; try lia.
assert (Hi: i + 1 - 1 = i) by lia.
rewrite Hi in H2; clear Hi.
lia.
Qed.

Lemma Znth_gt_sublist_gt :
  forall l i x key,
  0 <= i < Zlength l ->
  sorted l ->
  key < Znth i l ->
  In x (sublist i (Zlength l) l) ->
  key < x.
Proof.
intros.
apply (In_sorted_range _ _ _ _ H0) in H2; try lia.
Qed.

Lemma sublist_lt_0 : forall low high (l : list Z),
  low < 0 ->
  sublist low high l = sublist 0 high l.
Proof.
intros.
unfold sublist.
rewrite Z2Nat_neg; auto.
Qed.

Lemma Forall_sublist_overlap : forall (l : list Z) P low high,  
  high <= low ->
  Forall P (sublist high (Zlength l) l) ->
  Forall P (sublist low (Zlength l) l).
Proof.
intros l P low high Hle Hhigh.
case (Z_lt_dec high 0); intros.
  rewrite sublist_lt_0 in Hhigh; auto.
  case (Z_lt_dec low 0); intros; [rewrite sublist_lt_0; auto|].  
  apply Forall_forall.
  intros.
  assert (0 <= low) by lia.
  pose proof (Forall_forall P (sublist 0 (Zlength l) l)) as [Hp1 Hp2].
  specialize (Hp1 Hhigh).
  apply Hp1.
  revert H.
  apply sublist_In_sublist; auto with zarith.
assert (0 <= high) by lia.
apply Forall_forall; intros.
pose proof (Forall_forall P (sublist high (Zlength l) l)) as [Hp1 Hp2].
specialize (Hp1 Hhigh).
apply Hp1.
revert H0.
apply sublist_In_sublist; auto with zarith.
Qed.
