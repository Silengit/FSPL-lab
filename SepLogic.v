From FSPL Require Export Imp.
Import Omega.
(* First we define syntax of the language *)

(* We could reuse aexp and bexp defined for Imp. *)

(* Redefine commands here. To distinguish them 
   from Imp commands, we call them scom *)
(* You need to change it into an inductive definition *)
Inductive scom : Type :=
  | SSkip : scom
  | SAss : id -> aexp -> scom
  | SSeq : scom -> scom -> scom
  | SIf : bexp -> scom -> scom -> scom
  | SWhile : bexp -> scom -> scom
  | Lookup: id -> aexp -> scom
  | Mutate: aexp -> aexp -> scom
  | Alloc: id -> aexp -> aexp -> scom
  | Dealloc: aexp -> scom.

(* Program states, which is called sstate *)
Definition store := id -> nat.

(* if heap maps a natural number (address) to
   None, we say the address is not a valid address,
   or it is not in the domain of the heap *)
Definition heap := nat -> option nat.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

Lemma value_extensionality : forall {X Y: Type} {f g : X -> Y},
    f = g -> (forall (x: X), f x = g x).
Proof.
  intros X Y f g eql x. rewrite eql. reflexivity.
Qed.

(* Define an empty heap, which contains no memory cells *)
Definition emp_heap : heap := 
  fun (l: nat) => None.

Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.

Axiom heap_incomplete : forall (h: heap),
  exists l, not_in_dom l h /\ not_in_dom (l+1) h.

Theorem in_not_in_dec : 
  forall l h, {in_dom l h} + {not_in_dom l h}.
Proof.
  intros l h. unfold in_dom. unfold not_in_dom.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Defined.

(* h1 and h2 have disjoint domain *)
Definition disjoint (h1 h2: heap) : Prop := 
  forall l, not_in_dom l h1 \/ not_in_dom l h2.

(* union of two heaps *)
Definition h_union (h1 h2: heap) : heap :=
  fun l => 
    if (in_not_in_dec l h1) then h1 l else h2 l.

(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop := 
  forall l n, h1 l = Some n -> h2 l = Some n.

(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if eq_id_dec x x' then n else s x'.

(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else h l'.

(* heap dispose *)
Definition h_delete (h: heap) (l: nat) : heap :=
  fun l' => if eq_nat_dec l l' then None else h l'.

Definition sstate := (store * heap) %type.

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
  St:  sstate -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


(* Next we define the operational semantics *)

Notation "'SSKIP'" :=
  SSkip.
Notation "x ':::=' a" :=
  (SAss x a) (at level 60).
Notation "c1 ;;; c2" :=
  (SSeq c1 c2) (at level 80, right associativity).
Notation "'SWHILE' b 'DO' c 'END'" :=
  (SWhile b c) (at level 80, right associativity).
Notation "'SIFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (SIf c1 c2 c3) (at level 80, right associativity).
Notation "x ':::=' '[[' a ']]'" :=
  (Lookup x a) (at level 60).
Notation "'[[' e1 ']]' ':::=' e2" :=
  (Mutate e1 e2) (at level 60).
Notation "x ':::=' 'CONS(' e1 ',' e2 ')'" :=
  (Alloc x e1 e2) (at level 60).
Notation "'DISPOSE' '(' e ')'" :=
  (Dealloc e) (at level 60).

(* big-step semantics. You should change it into 
   an inductive definition *)

Reserved Notation "c1 '//' st '||' st'" (at level 40, st at level 39).
Inductive big_step: 
   scom * sstate -> ext_state -> Prop := 
  | B_Skip : forall st,
      SSKIP // st || St st
  | B_Ass  : forall s h a1 n x,
      aeval s a1 = n ->
      (x :::= a1) // (s,h) || St ((st_update s x n), h)
  | B_SeqNotAbort : forall c1 c2 st st' st'',
      c1 // st  || St st' ->
      c2 // st' || St st'' ->
      (c1 ;;; c2) // st || St st''
  | B_SeqAbort : forall c1 c2 st,
      c1 // st  || Abt ->
      (c1 ;;; c2) // st || Abt
  | B_IfTrue : forall s h st' b c1 c2,
      beval s b = true ->
      c1 // (s, h) || St st' ->
      (SIFB b THEN c1 ELSE c2 FI) // (s, h) || St st'
  | B_IfFalse : forall s h st' b c1 c2,
      beval s b = false ->
      c2 // (s, h) || St st' ->
      (SIFB b THEN c1 ELSE c2 FI) // (s, h) || St st'
  | B_WhileEnd : forall b s h c,
      beval s b = false ->
      (SWHILE b DO c END) // (s, h) || St(s, h) 
  | B_WhileLoopNotAbort : forall s h st' st'' b c,
      beval s b = true ->
      c // (s, h) || St st' ->
      (SWHILE b DO c END) // st' || St st'' ->
      (SWHILE b DO c END) // (s, h) || St st''
  | B_WhileLoopAbort : forall s h b c,
      beval s b = true ->
      c // (s, h) || Abt ->
      (SWHILE b DO c END) // (s, h) || Abt
  | B_LookupNotAbort : forall s h x e n,
      h (aeval s e) = Some n ->
      (x :::= [[e]]) // (s,h) || St ((st_update s x n), h)
  | B_LookupAbort : forall s h x e,
      h (aeval s e) = None ->
      (x :::= [[e]]) // (s,h) || Abt
  | B_MutateNotAbort : forall s h e l n e',
      aeval s e = l ->
      h l = Some n ->
      ([[e]] :::= e') // (s,h) || St (s, (h_update h l (aeval s e')))
  | B_MutateAbort : forall s h e l e',
      aeval s e = l ->
      h l = None ->
      ([[e]] :::= e') // (s,h) || Abt
  | B_Cons : forall s h e1 n1 e2 n2 l x,
      aeval s e1 = n1 ->
      aeval s e2 = n2 ->
      h l = None ->
      h (l+1) = None ->
      (x :::= CONS(e1, e2)) // (s,h) || St ((st_update s x l), (h_update (h_update h l n1) (l+1) n2))
  | B_DisposeSuc : forall s h e n,
      h (aeval s e) = Some n ->
      (DISPOSE (e)) // (s,h) || St (s, (h_delete h (aeval s e)))
  | B_DisposeFal : forall s h e,
      h (aeval s e) = None ->
      (DISPOSE (e)) // (s,h) || Abt  

   where "c1 '//' st '||' st'" := (big_step (c1,st) st').


(* small-step semantics. Should be inductive too *)

Reserved Notation "c1 '///' st '||' c2 '\\\' st'" (at level 40, st at level 39).
Inductive small_step: 
   scom * ext_state -> scom * ext_state -> Prop :=
  | S_Skip : forall st c1,
     (SSKIP ;;; c1) /// st || c1 \\\ st
  | S_Ass  : forall s h e n x,
      aeval s e = n ->
      (x :::= e) /// St(s,h) || SSKIP \\\ St ((st_update s x n), h)
  | S_SeqNotAbort : forall c1 c1' c2 st st',
      c1 /// St st  ||  c1' \\\ St st' ->
      (c1 ;;; c2) /// St st || (c1' ;;; c2) \\\ St st'
  | S_SeqAbort : forall c1 c1' c2 st,
      c1 /// St st  || c1' \\\ Abt ->
      (c1 ;;; c2) /// St st || SSKIP \\\ Abt
  | S_IfTrue : forall s h b c1 c2,
      beval s b = true ->
      (SIFB b THEN c1 ELSE c2 FI) /// St (s, h) || c1 \\\ St (s, h)
  | S_IfFalse : forall s h b c1 c2,
      beval s b = false ->
      (SIFB b THEN c1 ELSE c2 FI) /// St (s, h) || c2 \\\ St (s, h)
  | S_WhileEnd : forall b s h c,
      beval s b = false ->
      (SWHILE b DO c END) /// St (s, h) || SSKIP \\\ St (s, h) 
  | S_WhileLoop : forall s h b c,
      beval s b = true ->
      (SWHILE b DO c END) /// St (s, h) || (c;;;SWHILE b DO c END) \\\ St (s, h)
  | S_LookupNotAbort : forall s h x e n,
      h (aeval s e) = Some n ->
      (x :::= [[e]]) /// St (s,h) || SSKIP \\\ St ((st_update s x n), h)
  | S_LookupAbort : forall s h x e,
      h (aeval s e) = None ->
      (x :::= [[e]]) /// St (s,h) || SSKIP \\\ Abt
  | S_MutateNotAbort : forall s h e l n e',
      aeval s e = l ->
      h l = Some n ->
      ([[e]] :::= e') /// St (s,h) || SSKIP \\\ St (s, (h_update h l (aeval s e')))
  | S_MutateAbort : forall s h e l e',
      aeval s e = l ->
      h l = None ->
      ([[e]] :::= e') /// St (s,h) || SSKIP \\\ Abt
  | S_Cons : forall s h e1 n1 e2 n2 l x,
      aeval s e1 = n1 ->
      aeval s e2 = n2 ->
      h l = None ->
      h (l+1) = None ->
      (x :::= CONS(e1, e2)) /// St (s,h) || SSKIP \\\ St ((st_update s x l), (h_update (h_update h l n1) (l+1) n2))
  | S_DisposeSuc : forall s h e n,
      h (aeval s e) = Some n ->
      (DISPOSE (e)) /// St (s,h) || SSKIP \\\ St (s, (h_delete h (aeval s e)))
  | S_DisposeFal : forall s h e,
      h (aeval s e) = None ->
      (DISPOSE (e)) /// St (s,h) || SSKIP \\\ Abt  

  where "c1 '///' st '||' c2 '\\\' st'"  := (small_step (c1,st) (c2,st')).

(** Assertions **)
Definition sass := sstate -> Prop. 

(* define semantics of assertion emp *)
Definition emp : sass := 
    fun st: sstate => 
      snd st = emp_heap.

(* assertion e1 |-> e2 *)
Definition pto (e1 e2: aexp) : sass := 
    fun st: sstate =>
      match st with
      | (s, h) => h = h_update emp_heap (aeval s e1) (aeval s e2)
      end.
Notation "e1 '|->' e2" := (pto e1 e2) (at level 60).

(* p * q *)
Definition star (p q : sass) : sass := 
    fun st: sstate =>
      match st with
      | (s, h) => 
        exists h1, exists h2, 
          disjoint h1 h2 /\ h_union h1 h2 = h /\ p (s, h1) /\ q (s, h2)
      end.
Notation "p '**' q" := (star p q) (at level 70).

(* p --* q *)
Definition simp (p q: sass) : sass := 
  fun (st : sstate) =>
    match st with
    | (s, h) => 
      forall h', disjoint h' h -> p (s, h') -> q (s, h_union h h')
    end.
Notation "p '--*' q" := (simp p q) (at level 80).

Definition pure (p: sass) : Prop := 
  forall s h1 h2, p (s, h1) -> p (s, h2).

Definition precise (p: sass) : Prop := 
  forall h h1 h2 s, 
     h_subset h1 h 
     -> h_subset h2 h 
     -> p (s, h1) 
     -> p (s, h2)
     -> h1 = h2.

Definition intuitionistic (p: sass) : Prop := 
  forall s h h', p (s, h) -> disjoint h h' -> p (s, h_union h h').


(* continue here *)

Definition s_conj (p q: sass) : sass :=
  fun (s: sstate) => p s /\ q s.
Notation "p '//\\' q" := (s_conj p q) (at level 75).

Definition s_disj (p q: sass) : sass :=
  fun (s: sstate) => p s \/ q s.
Notation "p '\\//' q" := (s_disj p q) (at level 78).

Definition s_imp (p q: sass) : sass :=
  fun (s: sstate) => p s -> q s.
Notation "p '~~>' q" := (s_imp p q) (at level 85).

Definition strongerThan (p q: sass) : Prop :=
  forall s: sstate, s_imp p q s.
Notation "p '==>' q" := (strongerThan p q) (at level 90).

Definition spEquiv (p q: sass) : Prop :=
  (p ==> q) /\ (q ==> p).
Notation "p '<==>' q" := (spEquiv p q) (at level 90).

(* Prove the following lemmas *)
Lemma disj_star_distr: forall (p q r: sass),
  (p \\// q) ** r <==> (p ** r) \\// (q ** r).
Proof.
  intros p q r. unfold s_disj, star, strongerThan, s_imp.
  split; intros s; destruct s.
  - intros [h1 [h2 [H1 [H2 [ [Hp | Hq] Hr] ] ] ] ].
    + left. exists h1, h2; repeat split; try auto.
    + right. exists h1, h2; repeat split; try auto.
  - intros [H | H];
    destruct H as [h1 [h2 [H1 [H2 [H3 H4] ] ] ] ];
    exists h1, h2; repeat split; try auto.
Qed.

Lemma conj_star_distr: forall (p q r: sass),
  (p //\\ q) ** r ==> (p ** r) //\\ (q ** r).
Proof. 
  unfold s_conj, star, strongerThan, s_imp.
  intros p q r s. destruct s. intros H. 
  destruct H as [h1 [ h2 [H1 [H2 [ [H3 H4] H5] ] ] ] ].
  split; exists h1, h2; repeat split; try auto.
Qed.

Lemma commutitive_or: forall (p q: Prop),
  p \/ q -> q \/ p.
Proof.
  intros p q [Hp | Hq]; auto.
Qed.

Lemma silly_contradiction : forall l h,
  in_dom l h -> not_in_dom l h -> False.
Proof.
  intros l h H0 H1.
  unfold in_dom in H0.
  unfold not_in_dom in H1.
  rewrite H1 in H0. 
  destruct H0 as [n H].
  inversion H.
Qed.  

Lemma disjoint_union_equal : forall (h1 h2 : heap),
  disjoint h1 h2 -> h_union h1 h2 = h_union h2 h1.
Proof.
  intros h1 h2 HDis.
  apply functional_extensionality.
  intros n.  unfold h_union.
  destruct (in_not_in_dec n h1) eqn:E1.
  - destruct (in_not_in_dec n h2) eqn:E2.
    + unfold disjoint in HDis.
      assert( not_in_dom n h1 \/ not_in_dom n h2 ).
      { apply HDis. }
      exfalso.
      destruct H.
      * try apply silly_contradiction with n h1. 
        apply i. 
        apply H.
      * apply silly_contradiction with n h2. 
        apply i0.
        apply H.
    + reflexivity.
  - destruct (in_not_in_dec n h2) eqn:E2.
    + reflexivity.
    + unfold not_in_dom in n0, n1.
      rewrite n0, n1. reflexivity.
Qed.

Lemma union_trans_subset: forall (h1 h2 h: heap),
  disjoint h1 h2 -> (h_union h1 h2 = h) -> (h_subset h1 h) /\ (h_subset h2 h).
Proof.
  unfold h_subset.
  intros h1 h2 h. intros l.
  split.
  - intros addr n H1.
    induction H. unfold h_union.
    destruct (in_not_in_dec) eqn:E1.
    + apply H1.
    + assert (in_dom addr h1).
      { exists n. apply H1. }
      exfalso.
      apply silly_contradiction with addr h1. 
      apply H.
      apply n0.      
  - intros addr n H1.
    apply disjoint_union_equal in l.
    rewrite l in H. 
    unfold h_union in H.
    clear l.
    induction H.
    destruct (in_not_in_dec) eqn:E1.
    + apply H1.
    + assert (in_dom addr h2).
      { exists n. apply H1. }
      exfalso.
      apply silly_contradiction with addr h2. 
      apply H.
      apply n0.
Qed.

Lemma disjoint_equal : forall (h1 h2 : heap),
  disjoint h1 h2 -> disjoint h2 h1.
Proof.
  unfold disjoint, not_in_dom.
  intros h1 h2 H.
  intros l.
  assert(h1 l = None \/ h2 l = None).
  {apply H. }
  assert(h2 l = None \/ h1 l = None).
  {apply commutitive_or. apply H0. }
  apply H1.
Qed.

Lemma use_union_disjoint_prove_equality: forall (h1 h2 h3: heap),
  h_union h1 h2 = h_union h1 h3 /\
  (disjoint h1 h2) /\ (disjoint h1 h3) ->
  (h2 = h3).
Proof.
  intros h1 h2 h3 H.
  destruct H. destruct H0.
  apply functional_extensionality.
  unfold h_union in H.
  intros x.
  apply value_extensionality with x in H.
  destruct (in_not_in_dec) eqn:E1.
  - unfold disjoint in H0, H1.
    assert (not_in_dom x h1 \/ not_in_dom x h2).
    {apply H0. }
    assert (not_in_dom x h1 \/ not_in_dom x h3).
    {apply H1. }
    destruct H2.
    + exfalso. 
      apply silly_contradiction with x h1.
      apply i.
      apply H2. 
    + destruct H3.
      * exfalso.
        apply silly_contradiction with x h1.
        apply i.
        apply H3. 
      * rewrite H3, H2.
        reflexivity.
  - apply H.
Qed.


Lemma precise_conj_distr: forall (p q r: sass),
  precise r -> (p ** r) //\\ (q ** r) ==> (p //\\ q) ** r.
Proof.
  unfold s_conj, star, strongerThan, s_imp, precise.
  intros p q r. intros H. 
  intros s. destruct s. intros H0. destruct H0. destruct H0.
  destruct H0. destruct H0. destruct H2. destruct H3.
  destruct H1. destruct H1. destruct H1. destruct H5. destruct H6.
  assert (h_subset x h /\ h_subset x0 h).
  { apply union_trans_subset. assumption. apply H2. }
  destruct H8.
  assert (h_subset x1 h /\ h_subset x2 h).
  { apply union_trans_subset. assumption. apply H5. }
  destruct H10.
  assert(x0 = x2).
  { apply H with h s;
    try auto.
  }
  assert(x = x1).
  { symmetry in H5. rewrite disjoint_union_equal in H5. 
    rewrite disjoint_union_equal in H2.    
    rewrite H5 in H2.
    rewrite <- H12 in H2.
    apply use_union_disjoint_prove_equality with x0.
    split.
    - rewrite disjoint_union_equal.  
      rewrite disjoint_union_equal. apply H2. 
      apply H0. apply disjoint_equal. apply H0.
    - split. rewrite H12. rewrite H12 in H0.
      apply disjoint_equal. apply H0. 
      apply disjoint_equal. rewrite <- H12 in H1. apply H1.
    - apply H0.
    - apply H1.
  }
  exists x. exists x0. split.
  - apply H0.
  - split.
    + apply H2.
    + split.
      * split.
        apply H3.
        rewrite H13. 
        apply H6.
      * apply H4.
Qed.
  
 
Inductive multiStep : 
    scom * ext_state -> scom * ext_state -> Prop :=
| step0: forall c s, multiStep (c, s) (c, s)
| stepn: forall c s c' s' c'' s'', 
           small_step (c, s) (c', s')
           -> multiStep (c', s') (c'', s'')
           -> multiStep (c, s) (c'', s'').

(* c is safe at state s *)
Definition safeAt (c: scom) (s: sstate) : Prop :=
(* ~ multiStep (c, St s) Abt *) 
(*
forall c' s',
  multiStep (c, St s) (c', St s')
  -> c' = SKIP \/ exists c'', exists s'', small_step (c', St s') (c'', St s'').
*)
forall c' s',
  multiStep (c, St s) (c', St s')
  -> c' = SSKIP \/ exists c'', exists s'', small_step (c', St s') (c'', St s''). 

Definition safeMono (c: scom) : Prop := 
(*
  forall s h h', 
    safeAt c (s, h) -> disjoint h h' -> safeAt c (s, h_union h h').
*)
forall s h h', 
    safeAt c (s, h) -> disjoint h h' -> safeAt c (s, h_union h h').

Definition frame (c: scom) : Prop :=
  forall s h1 h2 c' s' h',
    safeAt c (s, h1) 
    -> disjoint h1 h2 
    -> small_step (c, St (s, h_union h1 h2)) (c', St (s', h'))
    -> exists h1', 
         small_step (c, St (s, h1)) (c', St (s', h1'))
         /\ disjoint h1' h2 
         /\ h_union h1' h2 = h'.

(*Lemma h_hat_not_used: forall c c' s s' h h' h_hat,
  disjoint h h_hat ->
  disjoint h' h_hat ->
  multiStep (c, St (s, h)) (c', St (s', h')) ->
  S(h_union h' h_hat)
  multiStep (c, St (s, (h_union h h_hat))) (c', St (s', (h_union h' h_hat))) . 
Proof.
Admitted.*)

Lemma multiframe : forall c s h1 h2 c' s' h',
   safeAt c (s, h1) -> 
   disjoint h1 h2 -> 
   multiStep (c, St (s, h_union h1 h2)) (c', St (s', h')) -> 
   exists h1', multiStep (c, St (s, h1)) (c', St (s', h1'))
      /\ disjoint h1' h2 
      /\ h_union h1' h2 = h'.
Proof.
Admitted.

Lemma smallsafeAt: forall c s s' h1 h2 h1' c',
  disjoint h1 h2 ->
  small_step (c, St (s, h1)) (c', St (s', h1')) ->
  exists st'', small_step (c, St (s, h_union h1 h2)) (c', St st'').
Proof.
  induction c;
  intros s s' h1 h2 h1' c' H1 H2; 
  try (inversion H2; eexists; constructor; eassumption).
  - inversion H2.
    + eexists. constructor.
    + destruct IHc1 with s s' h1 h2 h1' c1'; auto.
      eexists. constructor. apply H7.
  - inversion H2. subst; eexists.
    constructor. unfold h_union. destruct (in_not_in_dec (aeval s a) h1').
    + apply H0.
    + unfold not_in_dom in n0. rewrite n0 in H0. inversion H0.
  - inversion H2. eexists.
    apply S_MutateNotAbort with n.
    + inversion H2. apply H3.
    + unfold h_union. destruct in_not_in_dec.
      * auto.
      * unfold not_in_dom in n0. rewrite n0 in H9. inversion H9.
  - assert(exists l', not_in_dom l' (h_union h1 h2) /\ not_in_dom (l'+1) (h_union h1 h2)).
    {  apply heap_incomplete. }
    destruct H as [l H].
    inversion H2. eexists. 
    constructor; try eassumption.
    + destruct H. unfold not_in_dom in n. apply n.
    + destruct H. unfold not_in_dom in H14. apply H14.
  - inversion H2. eexists. apply S_DisposeSuc with n.
    unfold h_union. destruct in_not_in_dec.
    + auto.
    + unfold not_in_dom in n0. rewrite n0 in H0. inversion H0.
Qed.

Lemma safeMonoisTrue: forall c: scom, safeMono c.
Proof.
  unfold safeMono.
  intros c s h1 h2 H1 H2 c' st' H3.
  destruct st' as (s', h').
  assert( exists h1', multiStep (c, St (s, h1)) (c', St (s', h1'))
      /\ disjoint h1' h2 /\ h_union h1' h2 = h').
  { apply multiframe; auto. }
  unfold safeAt in H1.
  destruct H as [h1' H].
  destruct H as [H4 [H5 H6] ]. subst.
  assert(  c' = SSKIP \/ ((exists (c'' : scom)(st'' : sstate), c' /// St (s', h1') || c'' \\\ St st''))).
  { destruct H1 with c' (s', h1').
    - auto.
    - left. auto.
    - right. auto. 
  }
  destruct H.
  - left. auto.
  - right. destruct H as [c'' [ st'' H6] ].
    destruct st'' as (s'', h'').
    exists c''.
    apply smallsafeAt with s'' h''; auto.
Qed.

Lemma weak_safeAt: forall c s,
  safeAt c s
  -> c = SSKIP \/ exists c', exists s', small_step (c, St s) (c', St s'). 
Proof.
  unfold safeAt.
  intros c s H1.
  destruct H1 with c s.
  - apply step0.
  - left. auto.
  - right. auto.
Qed.

Lemma multiSeq: forall c c' s s' c'',
  multiStep (c, St s) (c', St s') ->
  multiStep (c;;; c'', St s) (c';;; c'', St s').
Proof.
Admitted.

Lemma safeAtSeq: forall c c' s h,
  safeAt (c ;;; c') (s, h) -> safeAt c (s,h).
Proof.
  unfold safeAt. intros c c' s h H1 c2 s' H2.
  apply multiSeq with (c'':=c') in H2.
  apply H1 in H2.
  destruct H2 as [H2 | [c'' [ s''  H2]  ] ];
  inversion H2.
  - left. auto.
  - right. subst. repeat eexists. eauto.
Qed.

Lemma frameLemma1: forall h1 h2 x n,
  in_dom x h1 -> disjoint h1 h2 -> h_union h1 h2 x = Some n -> 
  h1 x = Some n.
Proof.
  unfold h_union.
  intros h1 h2 x n H1 H2 H3.
  destruct (in_not_in_dec) eqn:E1.
  - auto.
  - exfalso. apply silly_contradiction with x h1; auto.
Qed.

Lemma frameLemma2: forall x e s h,
  safeAt (x :::= [[e]]) (s, h) ->
  in_dom (aeval s e) h.
Proof.
  intros x e s h H1.
  apply weak_safeAt in H1.
  destruct H1.
  - inversion H.
  - destruct H as [c' [s'  H1] ].
    inversion H1. subst. unfold in_dom. exists n. auto.
Qed.

Lemma frameLemma3: forall x e s h,
  safeAt ([[e]]:::= x) (s, h) ->
  in_dom (aeval s e) h.
Proof.
  intros x e s h H1.
  apply weak_safeAt in H1.
  destruct H1.
  - inversion H.
  - destruct H as [c' [s'  H1] ].
    inversion H1. subst. unfold in_dom. exists n. auto.
Qed.

Lemma frameLemma4: forall h1 h2 l s e,
  disjoint h1 h2 -> in_dom l h1 ->
  disjoint (h_update h1 l (aeval s e)) h2.
Proof.
  unfold h_update, disjoint.
  intros h1 h2 l s e H1 H2 x.
  unfold not_in_dom.
  destruct (Nat.eq_dec l x).
  - right. subst. destruct H1 with x.
    + exfalso. apply silly_contradiction with x h1; auto.
    + unfold not_in_dom in H. auto.
  - destruct H1 with x.
    + unfold not_in_dom in H. left. auto.
    + unfold not_in_dom in H. right. auto.  
Qed.

Lemma frameLemma5: forall h1 h2 l s,
  disjoint h1 h2 -> in_dom l h1 ->
  h_union (h_update h1 l s) h2 = h_update (h_union h1 h2) l s.
Proof.
  unfold disjoint, h_union, h_update.
  intros h1 h2 l s H1 H2.
  apply functional_extensionality.
  intros x.
  destruct (Nat.eq_dec l x).
  - destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec l l' then Some s else h1 l')) as [H3 | H4].
    + auto.
    + subst l.  unfold not_in_dom in H4. destruct (Nat.eq_dec x x). inversion H4. omega.
  - destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec l l' then Some s else h1 l')) as [H3 | H4].
    + destruct (in_not_in_dec x h1).
      * auto.
      * exfalso. unfold in_dom in H3. destruct (Nat.eq_dec l x). omega. 
        rewrite n0 in H3. destruct H3. inversion H.
    + destruct (in_not_in_dec x h1).
      * unfold not_in_dom in H4. destruct (Nat.eq_dec l x). omega.
        unfold in_dom in i. rewrite H4 in i. destruct i. inversion H.
      * auto.
Qed.

Lemma frameLemma7: forall h1 h2 l n1 n2,
  disjoint h1 h2 -> h1 l = None -> h2 l = None -> 
  h1 (l + 1) = None -> h2 (l+1) = None ->
  disjoint (h_update (h_update h1 l n1) (l + 1) n2) h2.
Proof.
  unfold disjoint, h_update.
  intros h1 h2 l n1 n2 H1 H2 H3 H4 H5 x.
  unfold not_in_dom. destruct (Nat.eq_dec (l + 1) x). subst.
  - right. auto.
  - destruct (Nat.eq_dec l x). subst.
    + right. auto.
    + destruct H1 with x.
      * left. unfold not_in_dom in H. auto.
      * right. unfold not_in_dom in H. auto.
Qed.

Lemma frameLemma7_1: forall h1 h2 l,
 h_union h1 h2 l = None -> h1 l = None.
Proof.
  unfold h_union.
  intros h1 h2 l H1.
  destruct (in_not_in_dec l h1).
  - auto.
  - unfold not_in_dom in n. auto. 
Qed.

Lemma frameLemma7_2: forall h1 h2 l,
 h_union h1 h2 l = None -> h2 l = None.
Proof.
  unfold h_union.
  intros h1 h2 l H1.
  destruct (in_not_in_dec l h1).
  - unfold in_dom in i. rewrite H1 in i. destruct i. inversion H.
  - auto.
Qed.

Lemma frameLemma8: forall h1 h2 l n1 n2,
  disjoint h1 h2 -> h1 l = None -> h2 l = None -> 
  h1 (l + 1) = None -> h2 (l+1) = None ->
  h_union (h_update (h_update h1 l n1) (l + 1) n2) h2 = h_update (h_update (h_union h1 h2) l n1) (l + 1) n2.
Proof.
  unfold h_union, disjoint, h_update.
  intros h1 h2 l n1 n2 H1 H2 H3 H4 H5.
  apply functional_extensionality. intros x.
  destruct (Nat.eq_dec (l+1) x).
  - destruct (Nat.eq_dec l x).
    + omega.
    + destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec (l + 1) l' then Some n2 else if Nat.eq_dec l l' then Some n1 else h1 l')).
      * auto.
      * unfold not_in_dom in n0. destruct (Nat.eq_dec (l+1) x).
        inversion n0. destruct (Nat.eq_dec l x); omega.
  - destruct (Nat.eq_dec l x).
    + destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec (l + 1) l' then Some n2 else if Nat.eq_dec l l' then Some n1 else h1 l')).
      * auto.
      * unfold not_in_dom in n0. destruct (Nat.eq_dec (l+1) x).
        inversion n0. destruct (Nat.eq_dec l x). inversion n0. omega.
    + destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec (l + 1) l' then Some n2 else if Nat.eq_dec l l' then Some n1 else h1 l')).
      * {unfold in_dom in i. destruct (Nat.eq_dec (l+1) x).
         - destruct (Nat.eq_dec l x); omega.
         - destruct (Nat.eq_dec l x).
           + omega.
           + destruct (in_not_in_dec x h1).
             * auto.
             * unfold not_in_dom in n5. rewrite n5 in i. 
               destruct i. inversion H.
        }
      * {unfold not_in_dom in n3. destruct (Nat.eq_dec (l+1) x).
         omega. destruct (Nat.eq_dec l x).
         - inversion n3.
         - destruct (in_not_in_dec x h1).
           + unfold in_dom in i. rewrite n3 in i. destruct i. inversion H.
           + auto.
        }
Qed. 

Lemma frameLemma9: forall a s h,
  safeAt (DISPOSE (a)) (s, h) ->
  in_dom (aeval s a) h.
Proof.
  intros a s h H1.
  apply weak_safeAt in H1.
  destruct H1.
  - inversion H.
  - destruct H as [c' [s'  H1] ].
    inversion H1. subst. unfold in_dom. exists n. auto.
Qed.

Lemma frameLemma10: forall h1 h2 l, 
  disjoint h1 h2 -> in_dom l h1 ->
  disjoint (h_delete h1 l) h2.
Proof.
  unfold disjoint, h_delete.
  intros h1 h2 l H1 H2 x.
  destruct H1 with x.
  - left. unfold not_in_dom. destruct (Nat.eq_dec) with l x.
    + auto.
    + unfold not_in_dom in H. auto.
  - right. auto.
Qed.

Lemma frameLemma11: forall h1 h2 l, 
  disjoint h1 h2 -> in_dom l h1 ->
  h_union (h_delete h1 l) h2 = h_delete (h_union h1 h2) l.
Proof.
  unfold disjoint, h_delete, h_union.
  intros h1 h2 l H1 H2.
  apply functional_extensionality. intros x.
  destruct (Nat.eq_dec l x).
  - destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec l l' then None else h1 l')).
    + auto.
    + unfold not_in_dom in n. destruct (Nat.eq_dec l x). subst.
      * destruct H1 with x. exfalso. apply silly_contradiction with x h1; auto.
        unfold not_in_dom in H. auto.
      * omega.
  - destruct (in_not_in_dec x (fun l' : nat => if Nat.eq_dec l l' then None else h1 l')).
    + unfold in_dom in i. destruct (Nat.eq_dec l x).
      * omega.
      * destruct H1 with x. exfalso. apply silly_contradiction with x h1; auto.
        unfold not_in_dom in H. destruct (in_not_in_dec x h1). auto.
        unfold not_in_dom in n1. rewrite n1 in i. destruct i. inversion H0.
    + unfold not_in_dom in n0.  destruct (Nat.eq_dec l x). omega.
      destruct (in_not_in_dec x h1).
      * unfold in_dom in i. rewrite n0 in i. destruct i. inversion H.
      * auto.
Qed.

Lemma frameisTrue: forall c: scom, frame c.
Proof.
    unfold frame. induction c;
    intros s h1 h2 c' s' h' H0 H1 H2;
    try (inversion H2; subst c');
    try (exists h1; repeat split; try assumption;
    constructor; assumption). 
  - destruct IHc1 with s h1 h2 c1' s' h';
    try assumption. 
    + apply safeAtSeq with c2. auto.
    + destruct H6 as [H8 [H9 H10 ] ]. exists x. repeat split; try assumption.
      constructor. try assumption.
  - exists h1. repeat split; try assumption.
    rewrite H8. subst s' h'. constructor. apply frameLemma1 with h2;
    try assumption. apply frameLemma2 with i. assumption.
  - exists (h_update h1 l (aeval s' a0)). repeat split; try assumption. subst s'.
    + apply S_MutateNotAbort with n; try assumption. apply frameLemma1 with h2;
      try assumption. rewrite <- H4. apply frameLemma3 with a0. assumption.
    + apply frameLemma4. assumption. subst. apply frameLemma3 with a0. auto.
    + apply frameLemma5. assumption. subst. apply frameLemma3 with a0. auto.
  - exists (h_update (h_update h1 l n1) (l + 1) n2). repeat split; try assumption.
    + constructor; try assumption.
      * apply frameLemma7_1 with h2. auto.
      * apply frameLemma7_1 with h2. auto.
    + apply frameLemma7. assumption. subst. 
      * apply frameLemma7_1 with h2. auto.
      * apply frameLemma7_2 with h1. auto.
      * apply frameLemma7_1 with h2. auto.
      * apply frameLemma7_2 with h1. auto.
    + apply frameLemma8. assumption. subst. 
      * apply frameLemma7_1 with h2. auto.
      * apply frameLemma7_2 with h1. auto.
      * apply frameLemma7_1 with h2. auto.
      * apply frameLemma7_2 with h1. auto.
  - exists (h_delete h1 (aeval s' a)). repeat split; try assumption.
    + apply S_DisposeSuc with n. apply frameLemma1 with h2;
      try assumption. subst s'. apply frameLemma9. assumption.
    + apply frameLemma10. assumption. subst. apply frameLemma9. auto.
    + apply frameLemma11. assumption. subst. apply frameLemma9. auto.
Qed.

Theorem locality: forall c : scom, safeMono c /\ frame c.
Proof.
  intros c. split.
  - apply safeMonoisTrue.
  - apply frameisTrue.
Qed.

