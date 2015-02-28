(********************
 * DM3: Omniscience
 *
 * L'objet de ce DM est d'étudier les types qui sont omniscients dans
 * la théorie des types sous-jacente de Coq. Un type [X] est
 * omniscient quand on peut décider pour tout prédicat [X → bool] s'il
 * est vrai partout ou non.  
*)

Set Implicit Arguments.
Require Import Coq.Unicode.Utf8.
Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.

(*****************)
(* Préliminaires *)
(*****************)

Lemma zero_or_succ : forall n : nat, n = 0 \/ exists n' : nat, n = S n'.
Proof.
  induction n.
    left. auto.
    destruct IHn.
      right. exists 0. auto.
      right. exists n. auto.
Qed.

Lemma exmid_bool : 
  forall a, a=true \/ a=false.
Proof.
  intro.
  assert ({a=true} + {a <> true}). apply bool_dec.
  destruct H.
    left. apply e.
    right. apply not_true_is_false. apply n.
Qed.

(*****************)

Record equivalence {X : Set} (R : X → X → Prop) : Set := 
  mkEq {
    refl: forall x, R x x;
    symm: forall x y, R x y -> R y x;
    trans: (forall x y z, R x y -> R y z -> R x z)
}.
Record setoid : Type := 
  mkSetoid {
    set : Set;
    R : set → set → Prop;
    R_eq : equivalence R
}.

Definition setoid_of_set (X : Set) : setoid.
  refine (mkSetoid (set:=X) (R := fun x y => x = y) _).
  apply mkEq; [auto | auto | apply eq_trans].
Defined.
Definition bool_setoid := setoid_of_set bool.
Definition nat_setoid := setoid_of_set nat.
Notation "'ℕ'" := (nat_setoid).

(*********************)
(*    Question 1.    *)
(*********************)

Definition extensional {X Y : setoid} (f : set X → set Y) :=
  forall x y, R X x y -> R Y (f x) (f y).
Hint Unfold extensional.
Definition arrow_setoid (X : setoid) (Y : setoid) : setoid.
refine (mkSetoid (set := { f : set X → set Y | extensional f })
                 (R := (fun f g => forall x : set X, R Y (proj1_sig f x) (proj1_sig g x)))
                 _).
apply mkEq.
  intros.
    apply R_eq.
  intros.
    apply symm.
    apply R_eq.
    apply H.
  intros.
    specialize H with (x0 := x0).
    specialize H0 with (x := x0).
    apply trans with (proj1_sig y x0).
    apply R_eq. apply H. apply H0.
Defined.
Notation "X ⇒ Y" := (arrow_setoid X Y) (at level 80).

Definition omniscient (X : setoid) :=
  forall p : set (X ⇒ bool_setoid), 
    (exists x, proj1_sig p x = false) \/ (forall x, proj1_sig p x = true).

(*********************)
(*    Question 2.    *)
(*********************)

Definition searchable (X : setoid) :=
  exists eps : set (X ⇒ bool_setoid) → set X, 
  forall p : set (X ⇒ bool_setoid),
    (proj1_sig p (eps p) = true <-> forall x, proj1_sig p x = true).

(*********************)
(*    Question 3.    *)
(*********************)

Lemma searchable_implies_omniscient : forall X, searchable X -> omniscient X.
Proof.
  intros. intro.
  unfold searchable in H.
  destruct H.
  specialize H with (p := p).
  assert (proj1_sig p (x p) = true \/ proj1_sig p (x p) = false).
    destruct (proj1_sig p (x p)). auto. auto.
  destruct H0.
    right. apply H. apply H0.
    left. exists (x p). apply H0.
Qed.

(*********************)
(*    Question 4.    *)
(*********************)

Definition finite_setoid (k: nat) : setoid.
refine (mkSetoid (set := { x | x ≤ k}) (R := (fun x y => proj1_sig x = proj1_sig y)) _).
split; [auto | auto | intros; apply eq_trans with (y := proj1_sig y); auto].
Defined.

Definition injection (n : nat) : { x : nat | x ≤ n } → { x : nat | x ≤ S n}.
  intro.
  destruct H.
  exists x. omega.
Defined.

(*****************************************************************)
(*  Preuve de la décidabilité de l'égalité de 2 preuves de n<=m. *)   
(*  Source : https://coq.inria.fr/V8.1/faq.html#le-uniqueness    *)
(*****************************************************************)

Require Import Eqdep_dec.
Require Import Peano_dec.

Theorem K_nat :
 forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof.
  intros; apply K_dec_set with (p := p).
  apply eq_nat_dec.
  assumption.
Qed.

Theorem eq_rect_eq_nat :
 forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
  intros; apply K_nat with (p := h); reflexivity.
Qed.

Scheme le_ind' := Induction for le Sort Prop.

Theorem le_uniqueness_proof : forall (n m : nat) (p q : n <= m), p = q.
Proof.
  induction p using le_ind'; intro q.
  replace (le_n n) with
    (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).
  2:reflexivity.
   generalize (refl_equal n).
     pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (le_Sn_n m); rewrite <- e; assumption.
  replace (le_S n m p) with
   (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
  2:reflexivity.
   generalize (refl_equal (S m)).
     pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
      contradiction (le_Sn_n m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
       rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
       rewrite (IHp l0); reflexivity.
Qed.

(** Fin de la preuve **)
 
Lemma finites_are_omniscient : forall k, omniscient (finite_setoid k).
Proof.

  induction k.
  
    intro.
    assert {x : nat | x ≤ 0}. exists 0. trivial.
    assert (proj1_sig p H = true \/ proj1_sig p H = false). apply exmid_bool.
    destruct H0.
      right.
        intro.
        destruct x.
        destruct H.
        assert (x0 = x). omega.
        subst x0.
        assert (proj1_sig p (exist (λ x : nat, x ≤ 0) x l0) = proj1_sig p (exist (λ x0 : nat, x0 ≤ 0) x l)).
          apply f_equal. apply f_equal.
          apply le_uniqueness_proof.
        rewrite H in H0.
        apply H0.
      left.
        exists H.
        apply H0.

    admit.
Qed.

(*********************)
(*    Question 5.    *)
(*********************)

Fixpoint min (f : nat → bool) (n:nat) := 
  match n with
    | 0 => f 0 
    | S n => andb (min f n) (f (S n))
  end.

(*********************)
(*    Question 6.    *)
(*********************)

Lemma min_trans :
  forall f n, min f (S n) = false -> min f n = false \/ (f (S n) = false).
Proof.
  intros.
  assert (min f (S n) = andb (min f n) (f (S n))). simpl (min f (S n)). trivial.
  rewrite H0 in H.
  apply andb_false_iff in H.
  destruct H.
  left. apply H.
  right. apply H.
Qed.

Lemma min_exact : 
  forall f n, f n = false -> min f n = false.
Proof.
  intro.
  induction n.
    intro. simpl. apply H.
    intro. simpl. rewrite H. apply andb_false_r.
Qed.

Lemma min_sup : 
  forall f n, min f n = false -> min f (S n) = false.
Proof.
  intro.
  induction n.
    intro. simpl. 
    assert (f 0 = false). apply H. 
    rewrite H0. apply andb_false_l.
    intro.
      simpl.
      assert (min f n && f (S n) = false). apply H.
      rewrite H0. apply andb_false_l.
Qed.

Lemma min_sup_sup : 
  forall f n m, min f n = false -> n <= m -> min f m = false.
Proof.
  intro. intro.
  induction m.
    intros.
      assert (n=0). omega.
      rewrite H1 in H. apply H.
    intros.
      assert (S m = n \/ n < S m). omega.
      destruct H1.
        rewrite H1. apply H.
        assert (min f m = false). apply IHm. apply H. omega.
        apply min_sup. apply H2.
Qed.

Lemma min_true : 
  forall f n, min f n = true -> forall k, k <= n -> f k = true.
Proof.
  intros.
  assert ((f k = true) \/ (f k = false)). apply exmid_bool.
  destruct H1.
    apply H1.
    exfalso.
    assert (min f n = false). apply min_sup_sup with (n := k). apply min_exact. apply H1. apply H0.
    apply eq_true_false_abs with (b:= min f n). apply H. apply H2.
Qed.
  
Lemma compute_minimum : 
  forall f n, min f n = false -> exists p, f p = false ∧ (forall k, k < p -> f k = true).
Proof.
  intro.
  induction n.
    intro. 
      exists 0. split. 
        apply H. 
        intros. exfalso. assert (k < 0 -> False). omega. apply H1. apply H0.
    intro.
      assert (min f n = false \/ (f (S n) = false)). apply min_trans. apply H.
      destruct H0.
        apply IHn. apply H0.
        assert (min f n = true \/ min f n = false). apply exmid_bool.
        destruct H1.
          exists (S n).
            split.
            apply H0.
            intros.
            assert (k <= n). omega.
            apply min_true with (n := n).
            apply H1. apply H3.
          apply IHn. apply H1.
Qed.

(*********************)
(*    Question 7.    *)
(*********************)

Definition Decreasing (α : nat -> bool) := 
  forall i k, i ≤ k -> α i = false -> α k = false.
Definition N_infty : setoid.
refine (mkSetoid 
          (set := { α : nat -> bool | Decreasing α })
          (R := fun α β => forall n : nat, proj1_sig α n = proj1_sig β n)
          _).
apply mkEq.
  intros. auto.
  intros. auto.
  intros.
    apply eq_trans with (proj1_sig y n).
    auto. auto.
Defined.
Notation "ℕ∞" := N_infty.
Notation "x ≡ y" := (R N_infty x y) (at level 80). (* ≡ représente l'égalité sur ℕ∞ *)

(*********************)
(*    Question 8.    *)
(*********************)

Definition ω : set ℕ∞.
refine (exist _ (fun x => true) _).
  intro. auto.
Defined.

(*********************)
(*    Question 9.    *)
(*********************)

Fixpoint lt_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => false
             | S m' => true
           end
    | S n' => match m with
                | O => false
                | S m' => lt_nat n' m'
              end
  end.

Lemma lt_inf : forall (n m : nat), n < m -> lt_nat n m = true.
Proof.
  induction n.
    induction m.
      intro. omega.
      intro. auto.
    induction m.
      intro. omega. 
      intro. simpl. apply IHn. omega.
Qed.

Lemma lt_sup : forall (n m : nat), n ≥ m -> lt_nat n m = false.
Proof.
  induction n.
    induction m.
      intro. auto.
      intro. omega.
    induction m.
      intro. auto. 
      intro. simpl. apply IHn. omega.
Qed.

Lemma lt_trans : forall (k n m : nat), lt_nat n k = false -> n ≤ m -> lt_nat m k = false.
Proof.
  induction k.
    intros.
      assert (m = 0 \/ exists m', m = S m'). apply zero_or_succ.
      destruct H1. rewrite H1. simpl. auto.
      destruct H1. rewrite H1. simpl. auto.
    intros. 
      assert (m = 0 \/ exists m', m = S m'). apply zero_or_succ.
      destruct H1. 
        rewrite H1. assert (0 = n). omega. rewrite H2. auto.
        destruct H1. rewrite H1. simpl. 
          assert (n = 0 \/ exists n', n = S n'). apply zero_or_succ.
           destruct H2.
             exfalso.
               assert (lt_nat n (S k) = true).
               rewrite H2. simpl. auto.
               apply eq_true_false_abs with (b := lt_nat n (S k)). auto. auto. 
             destruct H2.
             rewrite H2 in H.
             assert (lt_nat x0 k= false). apply H.
             apply IHk with (n := x0). apply H3. omega.
Qed.

Definition of_nat (k : nat) : set ℕ∞.
refine (exist _ (fun x => lt_nat x k) _).
  intro. intros.
  apply lt_trans with (n := i).
    apply H0. apply H.
Defined.

(**********************)
(*    Question 11.    *)
(**********************)

Definition p_set (x : nat → bool) : set (ℕ ⇒ bool_setoid).
  exists x.
  intro. intros.
  destruct H.
  apply R_eq.
Defined.

Fixpoint elt_ninf (f : nat -> bool) (n : nat) : bool :=
  match n with
    | O => f 0
    | S n' => andb (f (S n')) (elt_ninf f n') 
  end.

Lemma newZero : forall (p : nat -> bool) (n : nat),
  elt_ninf p n = true -> elt_ninf p (S n) = false -> p (S n) = false.
Proof.
  intros.
  assert (p (S n) && (elt_ninf p n) = false).
    apply H0.
  rewrite H in H1.
  assert (p (S n) && true = p (S n)).
  apply andb_true_r.
  rewrite H2 in H1.
  apply H1.
Qed.

Lemma alwaysZero : forall (p : nat -> bool) (n k: nat), 
  elt_ninf p n = false -> k >= n -> elt_ninf p k = false.
Proof.
  intro. intro.
  induction k.
    intros.
      assert (n = 0). omega.
      rewrite H1 in H.
      apply H.
    intros.
      assert (S k = n \/ S k > n). omega.
      destruct H1.
        rewrite H1.
          apply H.
        assert (elt_ninf p k = false).
          apply IHk.
          apply H.
          omega.
          simpl.
          rewrite H2.
          apply andb_false_r.
Qed.

Lemma mkDecreasing : forall p : nat -> bool, Decreasing (elt_ninf p).
Proof.
  intro.
  unfold Decreasing.
  induction i.
    intros.
      apply alwaysZero with (n := 0).
      apply H0.
      omega.
    intros.
      apply alwaysZero with (n := S i).
      apply H0.
      omega.
Qed.

Lemma zero_before : forall (p : nat -> bool) (m : nat),
  elt_ninf p m = false -> exists n, p n = false.
Proof.
  intro.
  induction m.
    intro.
      exists 0.
      destruct H.
      simpl. auto.
    intro.
      assert (p (S m) = false \/ elt_ninf p m = false).
        apply andb_false_iff.
        apply H.
        destruct H0.
          exists (S m).
            apply H0.
          apply IHm.
            apply H0.
Qed.

Lemma true_before : forall (p : nat -> bool) (n : nat),
  elt_ninf p n = true -> p n = true.
Proof.
  intros.
  assert (n = 0 \/ exists n', n = S n'). apply zero_or_succ.
  destruct H0.
    rewrite H0 in H.
      assert (elt_ninf p 0 = p 0). auto.
      rewrite H1 in H.
      rewrite H0.
      apply H.
    destruct H0.
      subst n.
      assert (p (S x) && elt_ninf p x = true).
        apply H.
      assert (p (S x) = true /\ elt_ninf p x = true).
        apply andb_true_iff. apply H0.
      destruct H1.
      apply H1.
Qed.    

Lemma almostDecreasing : forall (p : nat -> bool),
  (exists n, p n = false) <-> exists m, elt_ninf p m = false.
Proof.
  intro.
  split.
    intro.
      destruct H.
      exists x.
      assert (x = 0 \/ exists x', x = S x'). apply zero_or_succ.
      destruct H0.
        subst x.
          simpl. apply H.
        destruct H0.
          subst x.
          simpl.
          rewrite H.
          apply andb_false_l.
    intro.
      destruct H.
      apply zero_before with (m := x).
      apply H.
Qed.

Definition of_nat_of_p (p : nat -> bool) : set ℕ∞.
refine (exist _ (fun x => elt_ninf p x) _).
  apply mkDecreasing.
Defined.

Lemma false_after : forall (x : set ℕ∞) n k,
  proj1_sig x n = false -> k >= n -> proj1_sig x k = false.
Proof.
  intro. intro.
  induction k.
    intros.
      assert (n = 0). omega.
      rewrite H1 in H.
      apply H.
    intros.
      assert (S k = n \/ S k > n). omega.
      destruct H1.
        rewrite H1.
          apply H.        
        assert (proj1_sig x k = false).
          apply IHk.
          apply H. omega.
          destruct x.
          unfold Decreasing in d.
          apply d with (i := k).
          omega.
          apply H2.
Qed.
 
Lemma p_eq_of_nat : forall x : set ℕ∞,
  (exists n, x ≡ of_nat n) <-> (exists m, proj1_sig x m = false).
Proof.
  split.
    intro.
      destruct H.
      exists (S x0).
      rewrite H.
      simpl (proj1_sig (of_nat x0)).
      assert (lt_nat (S x0) x0 = false). apply lt_sup. omega.
      apply H0.
    intro.
      destruct H.
      assert (exists p, proj1_sig x p = false ∧ (forall k, k < p -> proj1_sig x k = true)).
        apply compute_minimum with (n := x0).
        apply min_exact.
        apply H.
      destruct H0.
      exists x1.
      simpl.
      intro.
      destruct H0.
      assert (n < x1 \/ n >= x1). omega.
      destruct H2.
        specialize (H1 n).
          assert (lt_nat n x1 = true). apply lt_inf. apply H2.
          rewrite H3.
          apply H1. apply H2.
        assert (lt_nat n x1 = false). apply lt_sup. apply H2.
          rewrite H3.
          apply false_after with (n := x1).
          apply H0. omega.
Qed.

Lemma p_eq_omega : forall x : set ℕ∞,
  (forall n, proj1_sig x n = true) <-> x ≡ ω.
Proof.
  intro.
  split.
    intro.
      intro.
      simpl.
      specialize (H n).
      apply H.
    intro.
      intro.
      rewrite H.
      simpl. auto.
Qed.

Lemma LPO_equiv : omniscient ℕ <-> forall x : set ℕ∞, x ≡ ω \/ exists k, x ≡ of_nat k.
Proof.
  split.
  
  intro. unfold omniscient in H.
  intro. destruct x. simpl.
  specialize (H (p_set x)). destruct H.
    right.
      destruct H.
      assert (exists p, (proj1_sig (p_set x)) p = false ∧ (forall k, k < p -> (proj1_sig (p_set x)) k = true)).
        apply compute_minimum with (n:= x0). apply min_exact. apply H.
      destruct H0.
      exists x1.
      intro.
      assert (n < x1 \/ n >= x1). omega. destruct H1.
        assert (lt_nat n x1 = true). apply lt_inf. apply H1. rewrite H2.
          destruct H0. apply H3. apply H1.
        assert (lt_nat n x1 = false). apply lt_sup. apply H1. rewrite H2.
          destruct H0.
          unfold Decreasing in d. specialize (d x1 n).
          apply d. omega. apply H0.
    left.
      intro.
      apply H. 
  
  intro. intro.
  simpl.
  destruct p. simpl.
  assert ((exists n, x n = false) <-> exists m, elt_ninf x m = false). apply almostDecreasing.
  destruct H0.
  specialize (H (of_nat_of_p x)).
  destruct H.
    right.
      assert (forall n, proj1_sig (of_nat_of_p x) n = true).
        apply p_eq_omega with (x := (of_nat_of_p x)).
        apply H.
      intro.
      specialize (H2 x0).
      apply true_before.
      apply H2.
    left.
      destruct H.
      exists x0.
      
      assert (x0 = 0 \/ exists x0', x0 = S x0'). apply zero_or_succ.
      destruct H2.
        specialize (H x0).
          assert (proj1_sig (of_nat x0) x0 = false).
          simpl.
          apply lt_sup. omega.
          rewrite H3 in H.
          subst x0.
          apply H.
        destruct H2.
          assert (elt_ninf x x1 = true).
            specialize (H x1).
            assert (proj1_sig (of_nat x0) x1 = true).
              simpl.
              apply lt_inf. omega.
            rewrite H3 in H.
            apply H.
          assert (elt_ninf x (S x1) = false).
            specialize (H (S x1)).
            assert (proj1_sig (of_nat x0) (S x1) = false).
              assert (S x1 = x0). omega. rewrite H4.
              simpl.
              apply lt_sup. omega.
            rewrite H4 in H.
            apply H.        
          assert (x (S x1) = false).
            apply newZero. apply H3. apply H4.
          assert (S x1 = x0). omega. rewrite H6 in H5.
          apply H5.
Qed.

(**********************)
(*    Question 13.    *)
(**********************)

Lemma eq_arrow : forall (p : set (ℕ∞ ⇒ bool_setoid)) x y,
  x ≡ y -> proj1_sig p x = proj1_sig p y.
Proof.
  intros.
  destruct p.
  simpl.
  apply e.
  apply H.
Qed.  

Lemma not_of_nat : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    (forall k, proj1_sig p (of_nat k) = true) -> 
    forall x, proj1_sig p x = false -> forall k, ~ (x ≡ of_nat k).
Proof.
  intros. intro.
  specialize (H k).
  assert (proj1_sig p x = proj1_sig p (of_nat k)).
    apply eq_arrow.
    apply H1.
  rewrite H2 in H0.
  apply eq_true_false_abs with (b := proj1_sig p (of_nat k)).
  apply H. apply H0.
Qed.

Lemma not_omega : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    proj1_sig p ω = true -> forall x, proj1_sig p x = false -> ~ (x ≡ ω).
Proof.
  intros. intro.
  assert (proj1_sig p x = proj1_sig p ω).
    apply eq_arrow.
    apply H1.
  rewrite H2 in H0.
  apply eq_true_false_abs with (b := proj1_sig p ω).
  apply H. apply H0.
Qed.

Lemma not_of_nat_k :
  forall x : set ℕ∞, 
    (forall k, ~ (x ≡ of_nat k)) -> forall k, proj1_sig x k = true.
Proof.
  intros.
  assert (proj1_sig x k = true \/ proj1_sig x k = false).
    apply exmid_bool.
  destruct H0.
    apply H0.
    assert (exists n, x ≡ of_nat n).  
      apply p_eq_of_nat. exists k.
      apply H0.
    destruct H1.
    specialize (H x0).
    exfalso.
    apply H. apply H1.
Qed.
 
Lemma not_of_nat_impl_omega :
  forall x : set ℕ∞, 
    (forall k, ~ (x ≡ of_nat k)) -> x ≡ ω.
Proof.
  intros.
  assert (forall k, proj1_sig x k = true).
    apply not_of_nat_k. apply H.
  intro.
  specialize (H0 n).
  simpl.
  rewrite H0.
  auto.
Qed.

Lemma density : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    proj1_sig p ω = true -> 
    (forall k, proj1_sig p (of_nat k) = true) -> 
    forall x, proj1_sig p x = true.
Proof.
  intros.
  assert (proj1_sig p x = false -> forall k, ~ (x ≡ of_nat k)). 
    intro. apply not_of_nat with (p:=p). apply H0. apply H1.
  assert ((forall k, ~ (x ≡ of_nat k)) -> x ≡ ω).
    apply not_of_nat_impl_omega.
  assert (proj1_sig p x = false -> x ≡ ω).
    intro. apply H2. apply H1. apply H3.
  assert (~ (proj1_sig p x = false)).
    intro. 
    assert (x ≡ ω). apply H3. apply H4.
    assert (proj1_sig p x = proj1_sig p ω).
      apply eq_arrow.
      apply H5.
    rewrite H6 in H4. rewrite H4 in H.
    assert (false <> true). auto.
    apply H7. apply H.
  destruct (proj1_sig p x).
  auto. auto.
Qed.

(**********************)
(*    Question 14.    *)
(**********************)

Definition ε (p : set (ℕ∞ ⇒ bool_setoid)) : set ℕ∞.
refine (exist _ (fun n => min (fun m => proj1_sig p (of_nat m)) n) _).
  intro. intros. 
  apply min_sup_sup with (n:= i). 
  assumption. assumption.
Defined.

(**********************)
(*    Question 15.    *)
(**********************)

Lemma ε_correct : forall p, proj1_sig p (ε p) = true <-> forall x, proj1_sig p x = true.
Proof. (* proj1_sig ajouté *)
  admit.
Qed.

(**********************)
(*    Question 16.    *)
(**********************)

Theorem N_infty_omniscient : omniscient ℕ∞.
Proof.
  apply searchable_implies_omniscient.
  exists ε.
  apply ε_correct.
Qed.

(**********************)
(*    Question 17.    *)
(**********************)

Lemma finite_falsification : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    (exists x, (¬ (x ≡ ω) /\ proj1_sig p x = false)) \/ (forall n, proj1_sig p (of_nat n) = true).
Proof.
  admit.
Qed.