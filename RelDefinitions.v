Require Export Coq.Program.Basics.
Require Export Coq.Classes.Morphisms.
Require Setoid.
Require Export Delay.

(** * Prerequisites *)

(** Some instances that would normally cause loops can be used
  nontheless if we insist that some parameters cannot be existential
  variables. One way to do this is to use this guard class, similar in
  spirit to [Unconvertible]. *)

Class NotEvar {A} (x: A).

Hint Extern 1 (NotEvar ?x) =>
  not_evar x; constructor : typeclass_instances.

(** Sometimes we may want to introduce an auxiliary variable to help
  with unification. *)

Class Convertible {A} (x y: A) :=
  convertible: x = y.

Hint Extern 1 (Convertible ?x ?y) =>
  eapply eq_refl : typeclass_instances.


(** * Relations *)

(** The constructions in [Coq.Relations.Relation_Definitions] are only
  concerned with relations within a single type, so that [relation A]
  is defined as [A -> A -> Prop]. We will need more general
  relations, and so I define [rel A B] as [A -> B -> Prop]. *)

(** When we move to a version of Coq with universe polymorphism, we
  can make this a [Polymorphic Definition]. In the meantime, we need
  to use a notation so that universes levels are instantiated at every
  use site. *)

Notation rel := (fun A1 A2 => A1 -> A2 -> Prop).

(** Note that the status of [rel] as a notation, rather than an actual
  definition, also prevents us from binding it to a [rel]
  scope. As a workaround, we open it as a global scope; in most places
  the [type] scope will override it as required. However this is an
  imperfect solutions, and means we must scope type explicitely here
  and there. *)

Delimit Scope rel_scope with rel.
Open Scope rel_scope.

(** ** Proof step *)

(** This is a catch-all class for any applicable strategy allowing us
  to make progress towards solving a relational goal. The proposition
  [P] should encode the new subgoals, in the format expected by
  [Delay.split_conjunction], and is decomposed accordingly in the
  [rstep] tactic.

  At the moment, the following priorities are used for our different
  [RStep] instances. Generally speaking, the most specific, quick
  tactics should be registered with higher priority (lower numbers),
  and the more general, slow tactics that are likely to instantiate
  evars incorrectly or spawn them too early should have lower priority
  (higher numbers):

    - 10 [RIntro]
    - 20 [Related]
    - 30 [preorder]
    - 40 [RDestruct]
    - 50 [Monotonicity] (includes [Reflexivity] -- we may want to split)
    - 70 [RExists] *)

Class RStep (P Q: Prop) :=
  rstep: P -> Q.

Ltac rstep :=
  lazymatch goal with
    | |- ?Q =>
      apply (rstep (Q := Q));
      Delay.split_conjunction
  end.

(** ** Proof automation *)

(** The following class solves the goal [Q] automatically. The
  typeclass resolution process allows for backtracking, trying every
  possible [RStep] at a given time. *)

Class RAuto (Q: Prop) :=
  rauto : Q.

Ltac rauto :=
  lazymatch goal with
    | |- ?Q =>
      apply (rauto (Q := Q));
      Delay.split_conjunction
  end.

(** After applying each step, we need to decompose the premise into
  individual subgoals, wrapping each one into a new [RAuto] goal so
  that the process continues. *)

Class RAutoSubgoals (P: Prop) :=
  rauto_subgoals : P.

Global Instance rauto_rstep P Q:
  RStep P Q ->
  RAutoSubgoals P ->
  RAuto Q.
Proof.
  firstorder.
Qed.

Ltac rauto_split :=
  red;
  Delay.split_conjunction;
  lazymatch goal with
    | |- ?Q => change (RAuto Q)
  end.

Hint Extern 1 (RAutoSubgoals _) =>
  rauto_split : typeclass_instances.

(** If [rauto] is run under the [delayed] tactical and we don't know
  how to make progress, bail out. Note that this will inhibit
  backtracking. *)

Hint Extern 1000 (RAuto _) =>
  red; solve [ delay ] : typeclass_instances.

(** ** Related elements *)

(** One of the simplest ways to solve a relational goal is to use a
  lemma from a database of known related terms. To register such
  lemmas we use the following typeclass. *)

Class Related {A B} (R: rel A B) (m1: A) (m2: B) := related_prf : R m1 m2.

Arguments Related {_ _} R%rel _ _.

Global Instance related_rstep {A B} (R: rel A B) m1 m2:
  Related R m1 m2 ->
  RStep True (R m1 m2) | 20.
Proof.
  firstorder.
Qed.

(** Conversely, when solving a goal of the form [Related ?R ?m ?n],
  go ahead and simply unfold [Related]. *)

Lemma unfold_related_rstep {A B} (R: rel A B) m n:
  RStep (R m n) (Related R m n).
Proof.
  firstorder.
Qed.

Hint Extern 1 (RStep _ (Related _ _ _)) =>
  eapply unfold_related_rstep : typeclass_instances.

(** ** Introduction rules *)

(** In effect, [RIntro] is pretty much identical to [RStep], but we
  like to separate introduction rules and the [rintro] tactic. *)

Class RIntro {A B} (P: Prop) (R: rel A B) (m: A) (n: B): Prop :=
  rintro: P -> R m n.

Ltac rintro :=
  lazymatch goal with
    | |- ?R ?m ?n =>
      apply (rintro (R:=R) (m:=m) (n:=n));
      Delay.split_conjunction
  end.

Global Instance rintro_rstep:
  forall `(RIntro), RStep P (R m n) | 10.
Proof.
  firstorder.
Qed.

(** Most introduction rules are entierly reversible. For instance,
  suppose we use the introduction rule for [++>] on a goal of the form
  [(R1 ++> R2) f g], to obtain [Hxy: R1 x y |- R2 (f x) (g y)]. If at
  a later stage we manage to prove our old goal [Hfg: (R1 ++> R2) f g],
  we can always use the elimination rule for [++>] in conjunction with
  the two hypotheses to prove [R2 (f x) (g y)].

  On the other hand, whenever a new existential variable is involved,
  this reversibility is lost: the time of introduction of the evar
  determines what a valid instantiation is, and there is no way to go
  back if we want to use components introduced later, say by
  destructing one of the hypotheses.

  For this reason, we want such introduction rules to be used only as
  a last resort, and segregate them as instances of the following
  class rather than [RIntro]. Moreover, to make sure that we don't
  leave the user in a dead-end, we only use it if we can immediately
  solve the resulting subgoal. *)

Class RExists {A B} (P: Prop) (R: rel A B) (m: A) (n: B): Prop :=
  rexists: P -> R m n.

Ltac reexists :=
  lazymatch goal with
    | |- ?R ?m ?n =>
      apply (rexists (R:=R) (m:=m) (n:=n));
      Delay.split_conjunction
  end.

Global Instance rexists_rstep {A B} P R (m:A) (n:B):
  RExists P R m n ->
  NonDelayed (RAutoSubgoals P) ->
  RStep True (R m n) | 70.
Proof.
  firstorder.
Qed.

(** ** Using relations *)

(** As we extend our relations language with new relators, we need to
  be able to extend the ways in which corresponding relational
  properties can be applied to a given goal. The following type class
  expresses that the relational property [R m n] can be applied to a
  goal of type [Q], generating the subgoal [P]. *)

Class RElim {A B} (R: rel A B) (m: A) (n: B) (P Q: Prop): Prop :=
  relim: R m n -> P -> Q.

Ltac relim H :=
  lazymatch goal with
    | |- ?Q =>
      apply (relim (Q:=Q) H)
  end.

(** The resolution process is directed by the syntax of [R]. We define
  an instance for each function relator. The base case simply uses the
  relational property as-is. *)

Global Instance relim_base {A B} (R: rel A B) m n:
  RElim R m n True (R m n).
Proof.
  firstorder.
Qed.

(** ** Destructing relational hypotheses *)

(** To make progress when the goal relates two pattern matching
  constructions, we need to show that the two matched terms are
  related, then destruct that hypothesis in a such a way that the two
  terms reduce to constructors.

  For most relators of inductive types, the constructors of the
  relator will simply follow the constructors of the corresponding
  type, so that destructing the relational hypothesis in the usual way
  will produce the desired outcome. However, sometimes it is more
  convenient to define such relators in a different way (see for
  instance [prod_rel]). In that case, we can use the following
  typeclass to specify an alternative way to destruct corresponding
  hypotheses.

  An instance of [RDestruct] is somewhat similar to a stylized
  induction principle. [T] expands to a conjunction of subgoals in the
  format expected by [Delay.split_conjunction]. For instance, the
  induction principle for [sum_rel] is:

  <<<
  sum_rel_ind:
    forall ...,
      (forall a1 a2, RA a1 a2 -> P (inl a1) (inl a2)) ->
      (forall b1 b2, RB b1 b2 -> P (inr b1) (inr b2)) ->
      (forall p1 p2, (RA + RB) p1 p2 -> P p1 p2)
  >>>

  A corresponding instance of [RDestruct] would be:

  <<<
  sum_rdestruct:
    RDestruct
      (sum_rel RA RB)
      (fun P =>
        (forall a1 a2, RA a1 a2 -> P (inl a1) (inl a2)) /\
        (forall b1 b2, RB b1 b2 -> P (inr b1) (inr b2)))
  >>>

  In the case of [sum_rel] however, which is defined as an inductive
  type with similar structure to [sum], we can rely on the default
  instance of [RDestruct], which simply uses the [destruct] tactic. *)

Class RDestruct {A B: Type} (R: rel A B) (T: rel A B -> Prop) :=
  rdestruct m n: R m n -> forall P, T P -> P m n.

Ltac rdestruct H :=
  lazymatch type of H with
    | ?R ?m ?n =>
      not_evar R;
      pattern m, n;
      apply (rdestruct (R:=R) m n H);
      clear H;
      Delay.split_conjunction
  end.

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

Lemma rdestruct_rstep {A B} m n (R: rel A B) P Q:
  RAuto (R m n) ->
  RDestruct R P ->
  P Q ->
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

(** ** Order on relations *)

(** This is our generalization of [subrelation]. Like the original it
  constitutes a preorder, and the union and intersection of relations
  are the corresponding join and meet. *)

Class subrel {A B} (R1 R2: rel A B) :=
  subrel_at x y: R1 x y -> R2 x y.

Arguments subrel {A B} R1%rel R2%rel.

Global Instance subrel_preorder A B:
  @PreOrder (rel A B) subrel.
Proof.
  split; firstorder.
Qed.

Instance subrel_refl {A B} (R: rel A B):
  subrel R R.
Proof.
  firstorder.
Qed.

Global Instance eq_subrel {A} (R: rel A A):
  Reflexive R ->
  subrel eq R.
Proof.
  intros HR x y H.
  subst.
  reflexivity.
Qed.

(** TODO: perhaps [subrel] doesn't need to be a class: we should drop
  the following instance and just use [Related subrel] for declaring
  subrelations. *)

Global Instance subrel_related {A B} (R R': rel A B):
  subrel R R' ->
  Related subrel R R'.
Proof.
  firstorder.
Qed.

(** ** Monotonicity properties *)

(** We use the following class for the user to declare monotonicity
  properties. This is a generalization of [Morphisms.Proper] from the
  Coq standard library: although we expect that most of the time the
  left- and right-hand side terms will be identical, they could be
  slightly different partial applications of the same function.

  Usually the differing arguments will be implicit, so that the user
  can still rely on the [Monotonic] notation below. Occasionally, you
  may need to spell out the two different terms and use the actual
  class [MonotonicPair] instead.

  Note that the argument order below eschews the precedent of
  [Morphisms.Proper] and our own [Related] class, which have the
  relation first, followed by the related term or terms. This is
  deliberate: we want the type parameters [A] and [B] to be unified in
  priority against the type of [f] and [g], rather than that of [R].
  In particular, the relator [forall_rel] yields an eta-expanded type
  of the form [(fun x => T x) x] for its arguments. When [A] and [B]
  take this peculiar form, instances declared using [forall_rel]
  become unusable (I assume because no second-order unification is
  performed when looking up the typeclass instance database). By
  contrast the type of [f] and [g] is much more likely to be in a
  "reasonable" form.

  We could flip those again in the [Monotonic] notation the the sake
  of aesthetics. But I feel it actually makes sense to list the
  monotonic function first, followed by the corresponding signature,
  akin to a typing judgement. *)

Class MonotonicPair {A B} (f: A) (g: B) (R: rel A B) :=
  monotonic: R f g.

Arguments MonotonicPair {_ _} _ _ R%rel.

Notation "'@' 'Monotonic' T m R" := (@MonotonicPair T T m m R)
  (at level 10, T at next level, R at next level, m at next level).

Notation Monotonic m R := (MonotonicPair m m R).

(** Another issue related to unification of type arguments: because
  [rel] is not a proper definition, sometimes Coq beta-reduces
  expressions spontaneously which interferes with typeclass
  resolution. As a result we need the following hint for
  [arrow_subrel] below to be used by the [monotonicity] tactic. When
  we upgrade to Coq 8.5 and make [rel] a universe-polymorphic
  definition instead of a notation, we can drop this. *)

Hint Extern 50 (MonotonicPair _ _ _) =>
  progress cbv beta : typeclass_instances.

(** For the sake of backwards compatibility, we override
  [Morphisms.Proper] with the following notation. However the plan is
  to drop this at some point, and perhaps even use [Proper] as a
  special case of [Related], so please do not rely on this. *)

Notation "'@' 'Proper' T R m" := (@Monotonic T m R)
  (at level 10, T at next level, R at next level, m at next level, only parsing).

Notation Proper R m := (Monotonic m R) (only parsing).
Notation Properish R m := (Monotonic m R) (only parsing).

(** As for [Related], we provide a [RStep] instance for unfolding
  [MonotonicPair]. *)

Lemma unfold_monotonic_rstep {A B} (R: rel A B) m n:
  RStep (R m n) (MonotonicPair m n R).
Proof.
  firstorder.
Qed.

Hint Extern 1 (RStep _ (MonotonicPair _ _ _)) =>
  eapply unfold_monotonic_rstep : typeclass_instances.


(** * Core relators *)

(** First, we introduce the core relators necessary for everything
  else, namely those for function types. The next section provides a
  more comprehensive library which covers many of the basic inductive
  type constructors as well. *)

(** *** Non-dependent function types *)

(** First, I define relators for non-dependent functions. This
  generalizes [respectful]. *)

Definition arrow_rel {A1 A2 B1 B2}:
  rel A1 A2 -> rel B1 B2 -> rel (A1 -> B1) (A2 -> B2) :=
    fun RA RB f g => forall x y, RA x y -> RB (f x) (g y).

Arguments arrow_rel {_ _ _ _} RA%rel RB%rel _ _.

Notation "RA ==> RB" := (arrow_rel RA RB)
  (at level 55, right associativity) : rel_scope.

Notation "RA ++> RB" := (arrow_rel RA RB)
  (at level 55, right associativity) : rel_scope.

Notation "RA --> RB" := (arrow_rel (flip RA) RB)
  (at level 55, right associativity) : rel_scope.

Global Instance arrow_subrel {A1 A2 B1 B2}:
  Proper (subrel --> subrel ++> subrel) (@arrow_rel A1 A2 B1 B2).
Proof.
  firstorder.
Qed.

Global Instance arrow_rintro {A1 A2 B1 B2} (RA: rel A1 A2) (RB: rel B1 B2) f g:
  RIntro (forall x y, RA x y -> RB (f x) (g y)) (RA ++> RB) f g.
Proof.
  firstorder.
Qed.

Lemma arrow_relim {A1 A2 B1 B2} RA RB f g m n P Q:
  @RElim B1 B2 RB (f m) (g n) P Q ->
  @RElim (A1 -> B1) (A2 -> B2) (RA ++> RB) f g (RA m n /\ P) Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (_ ++> _) _ _ _ _) =>
  eapply arrow_relim : typeclass_instances.

(** *** Dependent products *)

(** Now we consider the dependent case. The definition of [forall_rel]
  is somewhat involved, but you can think of relating [f] and [g] in
  the context of a structure-preserving transformation from a quiver
  ([V], [E]) to the quiver ([Type], [rel]). Like a functor, it has two
  components: [FV] maps nodes to types, and [FE] maps edges to
  relations. Then, [forall_rel FE f g] states that given an edge
  [(e : E v1 v2)], the images [f v1] and [g v2] are related by the
  corresponding relation [FE v1 v2 e]. We will write [forall_rel FE f g]
  as [(∀ e : E v1 v2, FE[v1,v2,e]) f g]. Notice that this notation
  binds [v1] and [v2] as well as [e].

  If that makes no sense, you can think of specific source quivers. So
  for instance, oftentimes we will want to use ([Type], [rel]) as the
  source quiver too. This corresponds to parametric polymorphism. The
  type of [Some] is [∀ A : Type, A -> option A]; the corresponding
  logical relation is [∀ R : rel A1 A2, R ++> option_rel R]. Stating
  that [Proper (∀ R : rel A1 A2, R ++> option_rel R) Some] means that,
  given any relation [R] and elements [x1] and [x2], if [R] relates
  [x1] and [x2], then [option_rel R] will relate [Some x1] and [Some x2].

  Another example from [liblayers] is the quiver of our data-indexed
  simulation relations [simrel : layerdata -> layerdata -> Type].
  Here the structure-preserving transformations are our simulation
  relation diagrams, which have types such as
  [lsim : forall D1 D2, simrel D1 D2 -> rel (layer D1) (layer D2)] or
  [psim : forall {D1 D2}, simrel D1 D2 -> rel (primsem D1) (primsem D2)].
  Then, the monotonicity of a data-indexed function —
  say, [foo: forall D : layerdata, layer D -> primsem D] —
  can be expressed as
  [Proper (∀ R : simrel D1 D2, siml D1 D2 R ++> simp D1 D2 R) foo].

  This definition is the same as [respectful_hetero]. *)

Definition forall_rel {V1 V2} {E: V1->V2->Type} {FV1: V1->Type} {FV2: V2->Type}:
    (forall v1 v2, E v1 v2 -> rel (FV1 v1) (FV2 v2)) ->
    rel (forall v1, FV1 v1) (forall v2, FV2 v2) :=
  fun FE f g =>
    forall v1 v2 (e: E v1 v2), FE v1 v2 e (f v1) (g v2).

Arguments forall_rel {_ _ _ _ _} FE%rel _ _.

Notation "∀  α : E v1 v2 , R" := (forall_rel (E := E) (fun v1 v2 α => R))
  (at level 200, α ident, E at level 7, v1 ident, v2 ident, right associativity)
  : rel_scope.

Notation "∀  α : E , R" := (forall_rel (E := E) (fun _ _ α => R))
  (at level 200, α ident, E at level 7, right associativity)
  : rel_scope.

Notation "∀  α , R" := (forall_rel (fun _ _ α => R))
  (at level 200, α ident, right associativity)
  : rel_scope.

Global Instance forall_rintro {V1 V2 E F1 F2} (FE: forall x y, _ -> rel _ _) f g:
  RIntro
    (forall u v e, FE u v e (f u) (g v))
    (@forall_rel V1 V2 E F1 F2 FE) f g.
Proof.
  firstorder.
Qed.

Lemma forall_relim {V1 V2 E FV1 FV2} R f g v1 v2 e P Q:
  RElim (R v1 v2 e) (f v1) (g v2) P Q ->
  RElim (@forall_rel V1 V2 E FV1 FV2 R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forall_rel _) _ _ _ _) =>
  eapply forall_relim : typeclass_instances.

(** ** Inverse relation *)

(** We use [flip] as our inversion relator. To this end we
  characterize its variance and introduce an [RElim] rule. *)

Global Instance flip_subrel {A B}:
  Proper (subrel ++> subrel) (@flip A B Prop).
Proof.
  firstorder.
Qed.

Lemma flip_rintro {A B} (R: rel A B) m n:
  RIntro (R n m) (flip R) m n.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RIntro _ (flip _) _ _) =>
  eapply flip_rintro : typeclass_instances.

Lemma flip_relim {A B} (R: rel A B) m n P Q:
  RElim R n m P Q ->
  RElim (flip R) m n P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (flip _) _ _ _ _) =>
  eapply flip_relim : typeclass_instances.
