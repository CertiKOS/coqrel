Require Export RelDefinitions.

Ltac default_rdestruct :=
  let m := fresh "m" in
  let n := fresh "n" in
  let Hmn := fresh "H" m n in
  let P := fresh "P" in
  let H := fresh in
  intros m n Hmn P H;
  revert m n Hmn;
  delayed_conjunction (intros m n Hmn; destruct Hmn; delay);
  pattern P;
  eexact H.

Hint Extern 100 (RDestruct _ _) =>
  default_rdestruct : typeclass_instances.

(** Sometimes we want to remember what the destructed terms were.
  We use the following relation. *)

Definition rdestruct_result {A B} m n (Q: rel A B) :=
  fun x y => m = x /\ n = y -> Q x y.

(* The default behavior is to simply discard the equations on the next
  step. However, if the user wants to keep them, they can declare an
  [rdestruct_remember] marker hypothesis to that end. *)

Lemma rdestruct_forget_rintro {A B} m n (Q: rel A B) x y:
  RIntro (Q x y) (rdestruct_result m n Q) x y.
Proof.
  firstorder.
Qed.

Lemma rdestruct_remember_rintro {A B} m n (Q: rel A B) x y:
  RIntro (m = x -> n = y -> Q x y) (rdestruct_result m n Q) x y.
Proof.
  firstorder.
Qed.

(** You can use the [rdestruct_remember] tactic to declare that
  hypothesis. *)

CoInductive rdestruct_remember := rdestruct_remember_intro.

Ltac rdestruct_remember :=
  lazymatch goal with
    | _ : rdestruct_remember |- _ =>
      idtac
    | _ =>
      let Hrdestruct := fresh "Hrdestruct" in
      pose proof rdestruct_remember_intro as Hrdestruct
  end.

(** The following hook switches between [rdestruct_forget] and
  [rdestruct_remember] as a result. *)

Ltac rdestruct_result_rintro :=
  lazymatch goal with
    | _ : rdestruct_remember |- _ => eapply rdestruct_remember_rintro
    | _ => eapply rdestruct_forget_rintro
  end.

Hint Extern 100 (RIntro _ (rdestruct_result _ _ _) _ _) =>
  rdestruct_result_rintro : typeclass_instances.

(** To use [RDestruct] instances to reduce a goal involving pattern
  matching [G] := [_ (match m with _ end) (match n with _ end)], we
  need to establish that [m] and [n] are related by some relation [R],
  then locate an instance of [RDestruct] that corresponds to [R]. It
  is essential that this happens in one step. At some point, I tried
  to split the process in two different [RStep]s, so that the user
  could control the resolution of the [?R m n] subgoal. However, in
  situation where [RDestruct] is not the right strategy, this may
  push a [delayed rauto] into a dead end. Thankfully, now we can use
  the [RAuto] typeclass to solve the [?R m n] subgoal in one swoop. *)

Lemma rdestruct_rstep {A B} m n (R: rel A B) P (Q: rel _ _):
  RAuto (R m n) ->
  RDestruct R P ->
  P (rdestruct_result m n Q) ->
  Q m n.
Proof.
  intros Hmn HR H.
  firstorder.
Qed.

Ltac use_rdestruct_rstep m n :=
  let H := fresh in
  intro H;
  pattern m, n;
  eapply (rdestruct_rstep m n);
  [ .. | eexact H].

Hint Extern 40 (RStep _ (_ (match ?m with _=>_ end) (match ?n with _=>_ end))) =>
  use_rdestruct_rstep m n : typeclass_instances.

(** In the special case where the terms matched on the left- and
  right-hand sides are identical, we want to destruct that term
  instead. At the moment, it's unclear to me whether this could be
  formulated as an [RDestruct] instance for [eq], or whether the
  process above could subsume this (we should conduct experiments with
  real code at some point). *)

Ltac destruct_rstep m :=
  let H := fresh in
  let n := fresh in
  intros H;
  generalize m;
  delayed_conjunction (intros n; destruct n; delay);
  eexact H.

Hint Extern 39 (RStep _ (_ (match ?m with _=>_ end) (match ?m with _=>_ end))) =>
  destruct_rstep m : typeclass_instances.
