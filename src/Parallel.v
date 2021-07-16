Require Import Recdef Omega.
Require Import ZtoConfl.
Require Import lex.

Inductive plex : Rel pterm :=
(* | pbvar: forall i, plex (pterm_bvar i) (pterm_bvar i) *)
| pvar: forall x, plex (pterm_fvar x) (pterm_fvar x)
| papp: forall m m' n n', plex m m' -> plex n n' -> plex (pterm_app m n) (pterm_app m' n')
| papp': forall m m' n n', plex m (pterm_abs m') -> plex n n' -> plex (pterm_app m n) (m' ^^ n')
| pabs: forall m m' L, (forall x, x \notin L -> plex (m^x) (m'^x)) ->
                  plex (pterm_abs m) (pterm_abs m')
| pabs': forall m m' n n' L, (forall x, x \notin L -> plex (m^x) (m'^x)) ->
                        plex n n' -> plex (pterm_app (pterm_abs m) n) (m' ^^ n')
| psub: forall m m' n n' L, (forall x, x \notin L -> plex (m^x) (m'^x)) ->
                       plex n n' -> plex (m[n]) (m' ^^ n').
Notation "t ===> u" := (plex t u) (at level 66).

(*** FLAVIO *)
Lemma lex_refltrans_abs: forall t t' L,
    (forall x, x \notin L -> (t^x) ->_lex* (t'^x)) -> pterm_abs t ->_lex* pterm_abs t'.
Proof. Admitted.

Lemma lex_refltrans_app_left: forall t t' u, t ->_lex* t' -> pterm_app t u ->_lex* pterm_app t' u.
Proof. Admitted.

Lemma lex_refltrans_app_right: forall u u' t, u ->_lex* u' -> pterm_app t u ->_lex* pterm_app t u'.
Proof. Admitted.

Lemma lex_refltrans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex* t'^x) -> (t[u]) ->_lex* (t'[u]). 
Proof. Admitted.

Lemma lex_refltrans_sub_in: forall u u' t, u ->_lex* u' -> (t[u]) ->_lex* (t[u']).
Proof. Admitted.

(* Lemma abc: forall m n, pterm_app (pterm_abs m) n ->_lex (m [n]). *)
(* Proof. *)

Lemma open_body_term: forall t t', body t -> term t' -> term (t ^^ t').
Proof. Admitted.

Lemma plex_regular: term_regular plex.
Proof.
  induction 1; intros.
  - split; apply term_var.
  - destruct IHplex1, IHplex2; split; apply term_app; auto.
  - split; destruct IHplex1, IHplex2.
    + apply term_app; auto.
    + apply open_body_term; auto; unfold body; inversion H2; subst; exists L; apply H6.
  - split; apply term_abs with (L := L); intros; destruct (H0 _ H1); auto.
  - destruct IHplex; split.
    + apply term_app; auto; apply term_abs with (L := L); intros; destruct (H0 _ H4); auto.
    + apply open_body_term; auto; unfold body; exists L; intros; destruct (H0 _ H4); auto.
  - destruct IHplex; split.
    + apply term_sub with (L := L); intros; [destruct (H0 _ H4)|]; auto.
    + apply open_body_term; auto; unfold body; exists L; intros; destruct (H0 _ H4); auto.
Qed.

Lemma plex_in_lex_refltrans:
  forall t t', t ===> t' -> t ->_lex* t'.
Proof.
  induction 1.
  - apply refl.
  - apply lex_refltrans_app_left with (u:=n) in IHplex1.
    apply lex_refltrans_app_right with (t := m') in IHplex2.
    apply refltrans_composition with (u := pterm_app m' n); assumption.
  - apply lex_refltrans_app_left with (u:= n) in IHplex1.
    apply lex_refltrans_app_right with (t := (pterm_abs m')) in IHplex2.
    apply refltrans_composition with (v := pterm_app (pterm_abs m') n') in IHplex1.
    clear IHplex2.
    + apply refltrans_composition with (u := pterm_app (pterm_abs m') n'); auto.
      apply rtrans with (b := m'[n']).
      * unfold lex. unfold red_ctx_mod_eqC. exists (pterm_app (pterm_abs m') n'). exists (m'[n']).
        split.
        -- reflexivity.
        -- split.
           ++ repeat constructor.
              ** apply plex_regular in H; destruct H; unfold body; inversion H1; subst.
                 exists L. assumption.
              ** apply plex_regular in H0; destruct H0; assumption.
           ++ reflexivity.
      * apply trans_to_refltrans; apply trans_ex_to_lex; apply full_comp;
          apply plex_regular in H0; apply plex_regular in H; destruct H, H0.
        -- inversion H1; subst; unfold body; exists L; assumption.
        -- assumption.
    + assumption.
  - apply lex_refltrans_abs with (L := L). assumption.
  - eapply lex_refltrans_abs in H0. apply lex_refltrans_app_left with (u := n) in H0.
    apply refltrans_composition with (v := pterm_app (pterm_abs m') n') in H0.
    + apply refltrans_composition with (u := pterm_app (pterm_abs m') n').
      * assumption.
      * apply rtrans with (b := pterm_sub m' n').
        -- unfold lex. unfold red_ctx_mod_eqC. exists (pterm_app (pterm_abs m') n'). exists (m'[n']).
           split. reflexivity. split. apply b_ctx_rule. apply ES_redex. constructor.
           unfold body. exists L. intros. specialize (H _ H2). apply plex_regular in H.
           destruct H. assumption.
           apply plex_regular in H1; destruct H1; assumption.
           reflexivity.
        -- apply trans_to_refltrans. apply trans_ex_to_lex. apply full_comp.
           ++ unfold body. exists L. intros. specialize (H _ H2). apply plex_regular in H. destruct H.
              assumption.
           ++ apply plex_regular in H1. destruct H1. assumption.
    + apply lex_refltrans_app_right. assumption.
  - apply lex_refltrans_sub with (u := n) in H0.
    apply lex_refltrans_sub_in with (t := m') in IHplex.
    apply refltrans_composition with (t := m[n]) in IHplex.
    + apply refltrans_composition with (u := m'[n']). assumption.
      apply trans_to_refltrans. apply trans_ex_to_lex. apply full_comp.
      * unfold body; exists L; intros; specialize (H _ H2); apply plex_regular in H; destruct H.
        assumption.
      * apply plex_regular in H1. destruct H1. assumption.
    + assumption.
Qed.
            
Fixpoint pterm_star (p : pterm) : pterm :=
  match p with
  | pterm_bvar i => pterm_bvar i
  | pterm_fvar x => pterm_fvar x
  | pterm_app m1 m2 => let pm := (pterm_star m1) in
                      match pm with
                      | pterm_abs m1' => m1' ^^ (pterm_star m2)
                      | _ => pterm_app (pterm_star m1) (pterm_star m2)
                      end
  | pterm_abs m => pterm_abs (pterm_star m)
  | pterm_sub m1 m2 => (pterm_star m1) ^^ (pterm_star m2)
  end.

Lemma star_open_rec: forall t n x,
    open_rec n (pterm_fvar x) (pterm_star t) = pterm_star (open_rec n (pterm_fvar x) t).
Proof.
  induction t; intros; simpl in *.
  - destruct (n0 === n).
    + simpl; reflexivity.
    + simpl; reflexivity.
  - reflexivity.
  - destruct (pterm_star t1) eqn:AA; try (simpl in *; rewrite <- IHt1; rewrite IHt2; reflexivity).
    + rewrite <- IHt1; simpl; destruct (n === n0); rewrite IHt2; reflexivity.
    + rewrite <- IHt1; unfold open; simpl. admit.
  - rewrite IHt; reflexivity.
  - unfold open; rewrite <- IHt1. admit.
Admitted.

Lemma star_open: forall t x, (pterm_star t)^x = pterm_star (t^x).
Proof. unfold open; intros; rewrite star_open_rec; auto. Qed.

Lemma plex_star: forall t, term t -> t ===> pterm_star t.
Proof.
  induction 1.
  - simpl. constructor.
  - simpl; destruct (pterm_star t1); simpl; constructor; auto.
  - simpl; apply pabs with (L := L); intros. erewrite star_open; eauto.
  - simpl; apply psub with (L := L); intros; try erewrite star_open; eauto.
Qed.

Lemma B_plex: forall a b, (a ->_B b) -> b ===> pterm_star a.
Proof.
  induction 1.
  - inversion H; subst; simpl; apply psub with (L := {}); intros.
    + rewrite star_open; auto; apply plex_star; apply open_body_term; auto.
    + apply plex_star; auto.
  - simpl; destruct (pterm_star t); constructor; auto; apply plex_star; auto.
  - apply plex_star in H0; simpl; destruct (pterm_star t); constructor; auto.
  - simpl; apply pabs with (L := L); intros; erewrite star_open; eauto.
  - simpl; apply psub with (L := L); intros; apply plex_star in H1; try erewrite star_open; eauto.
  - simpl; apply psub with (L := {}); intros; auto; rewrite star_open; auto.
    apply plex_star; apply open_body_term; auto.
Qed.

Lemma pterm_star_regular: forall t, term t -> term (pterm_star t).
Proof.
  induction 1; intros; simpl in *; auto.
  - destruct (pterm_star t1); simpl in *; try constructor; auto;
      apply open_body_term; unfold body; [inversion IHterm1; eexists; eassumption | idtac]; auto.
  - eapply term_abs; intros; rewrite star_open; eauto.
  - apply open_body_term; [unfold body; eexists; intros; rewrite star_open |]; eauto.
Qed.

Lemma plex_open_term: forall a b c d L,
    (forall x, x \notin L -> a^x ===> b^x) -> c ===> d -> (a ^^ c) ===> (b ^^ d).
Proof.
  intros; pick_fresh z; apply notin_union in Fr; destruct Fr;
    apply notin_union in H1; destruct H1; apply notin_union in H1; destruct H1;
      apply notin_union in H1; destruct H1.
  specialize (H _ H1); set (A:= a^z); replace (a^z) with (A). Admitted.
  (* -  *)
  (* -  *)

  
  (* induction a; intros; unfold open in *. *)
  (* - simpl in *; destruct n; pick_fresh z; apply notin_union in Fr; destruct Fr; *)
  (*   apply notin_union in H1; destruct H1; apply notin_union in H1; destruct H1. *)
  (*   + specialize (H _ H1). inversion H; subst. admit. *)
  (*   + apply notin_union in H1; destruct H1. specialize (H _ H1). apply plex_regular in H. *)
  (*     destruct H. inversion H. *)
  (* - simpl in *; pick_fresh z; apply notin_union in Fr; destruct Fr; *)
  (*     apply notin_union in H1; destruct H1; apply notin_union in H1; destruct H1; *)
  (*       apply notin_union in H1; destruct H1; specialize (H _ H1); inversion H. admit. *)
  (* - simpl in *; pick_fresh z; apply notin_union in Fr; destruct Fr; *)
  (*     apply notin_union in H1; destruct H1; apply notin_union in H1; destruct H1; *)
  (*       apply notin_union in H1; destruct H1; apply notin_union in H1; destruct H1; *)
  (*   specialize (H _ H1); inversion H; subst. *)
  (*   + *)

Lemma bswap_rec_term: forall t n, term t -> t = bswap_rec n t.
Proof. Admitted.
Lemma bswap_term: forall t, term t -> t = &t.
Proof. Admitted.

Lemma bswap_com_rec1: forall t v n, term v -> bswap_rec n ({n ~> v}t) = {S n ~> v}(bswap_rec n t).
Proof.
  induction t; intros.
  - simpl. destruct (n0 === n).
    + subst; simpl; destruct (n === n).
      * rewrite <- bswap_rec_term; auto.
      * congruence.
    + destruct n; simpl.
      * destruct (n0 === 0); simpl.
        -- congruence.
        -- reflexivity.
      * destruct (n0 === S n).
        -- congruence.
        -- destruct (n0 === n); subst; simpl.
           ++ destruct n.
              ** reflexivity.
              ** destruct (S n === n).
                 --- congruence.
                 --- reflexivity.
           ++ destruct (n0 === n).
              ** congruence.
              ** reflexivity.
  - simpl; reflexivity.
  - simpl; rewrite IHt1, IHt2; auto.
  - simpl; rewrite IHt; auto.
  - simpl; rewrite IHt1,IHt2; auto.
Qed.

Lemma bswap_com_rec2: forall t v n, term v -> {n ~> v}(bswap_rec n t) = bswap_rec n ({S n ~> v}t).
Proof.
  induction t; intros.
  - simpl. destruct (n0 === n).
    + destruct n.
      * subst; simpl; reflexivity.
      * destruct (n0 === n).
        -- simpl. destruct (n0 === S n0).
           ++ rewrite <- bswap_rec_term; auto.
           ++ subst. congruence.
        -- simpl. destruct (n0 === S n0).
           ++ congruence.
           ++ destruct (n0 === S n).
              ** reflexivity.
              ** congruence.
    + destruct n.
      * simpl. destruct (n0 === 0).
        -- congruence.
        -- reflexivity.
      * destruct (n0 === n).
        -- simpl; destruct (n0 === n0).
           ++ rewrite <- bswap_rec_term; auto.
           ++ congruence.
        -- simpl. destruct (n0 === S n).
           ++ congruence.
           ++ destruct (n0 === n).
              ** congruence.
              ** reflexivity.
  - simpl. reflexivity.
  - simpl; rewrite IHt1, IHt2; auto.
  - simpl; f_equal; rewrite (IHt _ _ H); auto.
  - simpl; rewrite IHt1, IHt2; auto.
Qed.

Lemma bswap_com1: forall t v, term v -> {0 ~> v}(&t) = &({1 ~> v}t).
Proof. unfold bswap; intros; apply bswap_com_rec2; auto. Qed.

Lemma bswap_com2: forall t v, term v -> &({0 ~> v}t) = {1 ~> v}(&t).
Proof. unfold bswap; intros. apply bswap_com_rec1; auto. Qed.

Lemma bswap_rec_lc: forall t v n, lc_at (S n) t -> {n ~> v}t = {(S n) ~> v}(bswap_rec n t).
Proof.
  induction t; intros.
  - simpl in *. destruct (n0 === n).
    + subst; simpl. destruct (n === n).
      * reflexivity.
      * congruence.
    + destruct n.
      * simpl. reflexivity.
      * destruct (n0 === n).
        -- subst. omega.
        -- simpl. destruct (n0 === n).
           ++ congruence.
           ++ reflexivity.
  - simpl; reflexivity.
  - simpl in *; destruct H; rewrite IHt1, IHt2; auto.
  - simpl in *; rewrite IHt; auto.
  - simpl in *; destruct H; rewrite IHt1,IHt2; auto.
Qed.

Lemma bswap_open1: forall t v, lc_at 1 t -> {0 ~> v}t = {1 ~> v}(&t).
Proof. unfold bswap; intros; apply bswap_rec_lc; auto. Qed.

Lemma subst_com:
  forall (i j : nat) (t u v : pterm),
  i <> j -> term u -> term v -> {i ~> u}({j ~> v}t) = {j ~> v}({i ~> u}t). Admitted.

Lemma open_bswap1:
  forall (n : nat) (t u v : pterm), term v -> {S n ~> u}({n ~> v}t) = {n ~> u}({S n ~> v}bswap_rec n t).
Admitted.

Lemma open_bswap2:
  forall (n : nat) (t u v : pterm), term v -> {n ~> u}({S n ~> v}t) = {S n ~> u}({n ~> v}bswap_rec n t).
Admitted.

(* Lemma bswap_star: forall t, lc_at 2 t -> pterm_star (&t) = &(pterm_star t). *)
(* Proof. *)
(*   induction t; unfold bswap in *. *)
(*   - admit. *)
(*   - admit. *)
(*   - intros; simpl in *; rewrite IHt1. *)
(*     + destruct (pterm_star t1); simpl in *. *)
(*       * admit. *)
(*       * admit. *)
(*       * admit. *)
(*       *  *)

(* Lemma bswap_rec_open_rec: forall t u n, term u -> {n ~> u}(bswap_rec (S n) t) = bswap_rec n ({n ~> u}t). *)
(* Proof. *)
(*   induction t; intros. *)
(*   - destruct (n0 === n). *)
(*     + subst. simpl. *)
(*       * destruct n. *)
(*         -- simpl. admit. *)
(*         -- destruct (S n === n). *)
(*            ++ omega. *)
(*            ++ destruct n. *)
(*               ** simpl. admit. *)
(*               ** destruct (S (S n) === n). *)
(*                  --- omega. *)
(*                  --- destruct (S (S n) === S (S n)). *)
(*                      +++ simpl. destruct (n === n). *)
(*                          *** admit. *)
(*                          *** congruence. *)
(*                      +++ omega. *)
(*     + simpl. destruct n. *)
(*       * destruct (n0 === 0). *)
(*         -- congruence. *)
(*         -- simpl. destruct (n0 === 0). *)
(*            ++ congruence. *)
(*            ++ reflexivity. *)
(*       * destruct (n0 === n). *)
(*         -- destruct (n0 === S n). *)
(*            ++ congruence. *)
(*            ++ simpl; subst. *)
    (* + destruct (n0 === 0); subst. *)
    (*   * simpl. admit. *)
    (*   * simpl. destruct (n0 === 0). *)
    (*     -- congruence. *)
    (*     -- reflexivity. *)
    (* + destruct (n0 === n). *)
    (*   * destruct (n0 === S n). *)
    (*     -- omega. *)
    (*     -- subst. simpl. destruct (n === S (S n)). *)
    (*        ++ omega. *)
    (*        ++ destruct (n === S n). *)
    (*           ** congruence. *)
    (*           ** destruct (n === n). *)
    (*              ---  *)

Lemma bswap_star: forall t, pterm_star (&t) = &(pterm_star t).
Proof. Admitted.
(*   induction t. *)
(*   - unfold bswap; simpl. destruct n. *)
(*     + reflexivity. *)
(*     + destruct n. *)
(*       * reflexivity. *)
(*       * reflexivity. *)
(*   - unfold bswap; simpl; reflexivity. *)
(*   - unfold bswap in *; simpl; rewrite IHt1; destruct (pterm_star t1); simpl in *. *)
(*     + destruct n. *)
(*       * simpl; rewrite IHt2; reflexivity. *)
(*       * destruct n; rewrite IHt2; reflexivity. *)
(*     + rewrite IHt2; reflexivity. *)
(*     + rewrite IHt2; reflexivity. *)
(*     +  *)
(*     + admit. *)
(*   - admit. *)
(*   - admit. *)

    
(* (*   - unfold bswap in *; simpl; rewrite IHt1; destruct (pterm_star t1). *) *)
(* (*     + admit. *) *)
(* (*     + admit. *) *)
(* (*     + admit. *) *)
(* (*     + unfold open; simpl. *) *)
(* (* Admitted. *) *)
(* Admitted. *)
  
        
(* Lemma bswap_rec_star: forall t n, pterm_star (bswap_rec n t) = bswap_rec n (pterm_star t). *)
(* Proof. *)
(*   induction t; intros. *)
(*   - simpl; destruct (n0 === n). *)
(*     + reflexivity. *)
(*     + destruct n. *)
(*       * reflexivity. *)
(*       * destruct (n0 === n). *)
(*         -- reflexivity. *)
(*         -- reflexivity. *)
(*   - reflexivity. *)
(*   - simpl; rewrite IHt1; destruct (pterm_star t1) eqn:Hd. *)
(*     + simpl. destruct (n === n0). *)
(*       * rewrite IHt2; reflexivity. *)
(*       * destruct n0. *)
(*         -- rewrite IHt2; reflexivity. *)
(*         -- destruct (n === n0). *)
(*            ++ rewrite IHt2; reflexivity. *)
(*            ++ rewrite IHt2; reflexivity. *)
(*     + simpl. rewrite IHt2; reflexivity. *)
(*     + simpl. rewrite IHt2; reflexivity. *)
(*     + simpl; unfold open; simpl in *. rewrite IHt2. *)
(* Admitted. *)

Lemma sysx_plex: forall a b, (sys_x a b) -> b ===> pterm_star a.
Proof.
  intros a b Hsys; assert (Hsyss: sys_x a b). assumption. induction Hsys. intros.
  - simpl; unfold open; simpl. apply plex_star; auto.
  - simpl; unfold open; rewrite open_rec_term;
      [apply plex_star | apply pterm_star_regular]; auto.
  - simpl. destruct (pterm_star t1) eqn:AA.
    + change ((pterm_app (pterm_bvar n) (pterm_star t2) ^^ pterm_star u)) with (pterm_app (pterm_bvar n ^^ pterm_star u) ((pterm_star t2)^^pterm_star u)).
      constructor. unfold open.
      -- rewrite <- AA; unfold body in *; destruct H; apply psub with (L := x).
         ++ intros; rewrite star_open; apply plex_star; apply H; auto.
         ++ apply plex_star; auto.
      -- unfold body in *; destruct H0; apply psub with (L := x); intros.
         ++ rewrite star_open; apply plex_star; apply H0; auto.
         ++ apply plex_star; auto.
    + change ((pterm_app (pterm_fvar v) (pterm_star t2) ^^ pterm_star u)) with (pterm_app ((pterm_fvar v)^^ pterm_star u) ((pterm_star t2)^^ pterm_star u));   
        unfold open; constructor.
      * rewrite <- AA. unfold body in *; destruct H; apply psub with (L := x).
        -- intros; rewrite star_open; apply plex_star; apply H; auto.
        -- apply plex_star; auto.
      * unfold body in *; destruct H0; apply psub with (L := x).
        -- intros; rewrite star_open; apply plex_star; apply H0; auto.
        -- apply plex_star; auto.
    + change (pterm_app (pterm_app p1 p2) (pterm_star t2) ^^ pterm_star u) with (pterm_app ((pterm_app p1 p2)^^ pterm_star u) ((pterm_star t2)^^ pterm_star u)); constructor.
      * rewrite <- AA. unfold body in *; destruct H; apply psub with (L := x).
        -- intros; rewrite star_open; apply plex_star; apply H; auto.
        -- apply plex_star; auto.
      * unfold body in *; destruct H0; apply psub with (L := x).
        -- intros; rewrite star_open; apply plex_star; apply H0; auto.
        -- apply plex_star; auto.
    + admit. 
    + rewrite <- AA; unfold open; simpl; constructor.
      * unfold body in *; destruct H; apply psub with (L := x).
        -- intros; rewrite star_open; apply plex_star; apply H; auto.
        -- apply plex_star; auto.
      * unfold body in *; destruct H0; apply psub with (L := x).
        -- intros; rewrite star_open; apply plex_star; apply H0; auto.
        -- apply plex_star; auto.
  - simpl; unfold open; simpl; apply pabs with (L := {}); intros;
      assert (HH: pterm_star ((& t [u]) ^ x) = ({1 ~> pterm_star u} pterm_star t) ^ x).
    + unfold open; simpl; rewrite (open_rec_term u); auto; unfold open.
      rewrite subst_com; auto.
      * rewrite open_bswap1; auto; f_equal; rewrite <- star_open_rec; unfold bswap; f_equal;
          apply bswap_star.
      * apply pterm_star_regular; auto.
    + rewrite <- HH; apply plex_star. admit.
  - admit.



    
  (* - admit. *)
  (* - simpl; unfold open; simpl. apply pabs with (L := {}); intros; unfold open; simpl. *)
  (*   rewrite <- bswap_open; auto. admit. *)
  (* - simpl. admit. *)
Admitted.

Lemma x_plex: forall a b, (a ->_x b) -> b ===> pterm_star a.
Proof.
  induction 1.
  - apply sysx_plex; auto.
  - simpl; destruct (pterm_star t); constructor; auto; apply plex_star; auto.
  - apply plex_star in H0; simpl; destruct (pterm_star t); constructor; auto.
  - simpl; apply pabs with (L := L); intros; erewrite star_open; eauto.
  - apply plex_star in H1; simpl; apply psub with (L := L); intros; try erewrite star_open; eauto.
  - simpl; apply psub with (L := {}); intros. try erewrite star_open. eauto.
    apply plex_star; apply open_body_term; auto.
Qed.      

Lemma lex_plex: forall a b, (a ->_lex b) -> b ===> pterm_star a.
Proof.
  destruct 1. destruct H. destruct H. destruct H0. rewrite <- H in H0. rewrite H1 in H0. destruct H0.
  - apply B_plex; auto.
  - apply x_plex; auto.
Qed.

Lemma plex_plex: forall a b, a ===> b -> b ===> pterm_star a.
Proof.
  induction 1.
  - simpl; constructor.
  - simpl; destruct (pterm_star m); constructor; auto.
  - inversion IHplex1; subst; simpl; destruct (pterm_star m); try inversion H2; subst.
    apply plex_open_term with (L := L); auto.
  - simpl; apply pabs with (L := L); intros; erewrite star_open; eauto.
  - simpl; apply plex_open_term with (L := L); auto; intros; erewrite star_open; eauto.
  - simpl; apply plex_open_term with (L := L); auto; intros; erewrite star_open; eauto.
Qed.            

Lemma BxZpterm_star :
  forall a b : pterm,
    a ->_lex b -> refltrans lex b (pterm_star a) /\ refltrans lex (pterm_star a) (pterm_star b).
Proof.
  intros; split.
  - apply plex_in_lex_refltrans; apply lex_plex in H; assumption.
  - apply lex_plex in H; apply plex_in_lex_refltrans; apply plex_plex in H; assumption.
Qed.                                       
  
TheoreM Zlex: Zprop lex.
Proof.
  unfold Zprop.
  exists pterm_star.
  apply BxZpterm_star.
Qed.
