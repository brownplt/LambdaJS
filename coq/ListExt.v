Require Import Coq.Logic.Decidable.
Require Import SfLib.
Set Implicit Arguments.

Fixpoint lookup_assoc A B (l : list (A * B)) k default (eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) : B
  := match l with
       | [] => default
       | (k',v)::tl => if (eq_dec k k') then v else lookup_assoc tl k default eq_dec
     end.
Fixpoint update_assoc A B (l : list (A * B)) k v (eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) : list (A*B)
  := match l with
       | [] => []
       | (k',o)::tl => if (eq_dec k k') then (k',v)::tl else (k',o)::(update_assoc tl k v eq_dec)
     end.
Fixpoint remove_fst A B (x : A) (l : list (A*B)) (eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}): list (A*B) :=
    match l with
      | [] => []
      | (y,b)::tl => if (eq_dec x y) then remove_fst x tl eq_dec else (y,b)::(remove_fst x tl eq_dec)
    end.

Lemma in_dec_dec_list :
  (forall A (l1 : list A) l2, (forall a1 a2, In a1 l1 -> In a2 l2 -> a1 = a2 \/ a1 <> a2) -> (l1 = l2 \/ l1 <> l2)).
Proof with eauto.
induction l1. intros. destruct l2; [left; auto | right; congruence].
induction l2. intros. right; congruence. intros. assert (a = a0 \/ a <> a0). apply H; constructor...
assert (l1 = l2 \/ l1 <> l2). apply IHl1. intros. apply H. right... right...
inversion H0; subst.  inversion H1; subst. left; auto. right; congruence. right; congruence.
Qed.

Lemma forall_dec_dec_exists : forall A (P : A -> Prop) (l : list A), (forall a1 a2 : A, a1 = a2 \/ ~ a1 = a2) 
  -> Forall (fun e => P e \/ ~ P e) l
  -> decidable (exists e, In e l /\ P e).
Proof with eauto.
intros. unfold decidable in *. induction H0. right; intro. inversion H0. inversion H1. inversion H2.
inversion H0. left. exists x. split... constructor...
inversion IHForall. inversion H3. left; exists x0. inversion H4; split... assert (D := H x x0). 
destruct D. subst. contradiction. right. auto.
right. intro. apply H3. inversion H4. exists x0. inversion H5; split... assert (D := H x x0). 
destruct D. subst. contradiction. inversion H6. contradiction. auto.
Qed.

Lemma forall_dec_dec_forall : forall A (P : A -> Prop) (l : list A), 
  Forall (fun e => P e \/ ~ P e) l -> (Forall P l) \/ ~ (Forall P l).
Proof with eauto.
induction l. intros. left; constructor.
intros. inversion H.
assert (Forall P l \/ ~ Forall P l). apply IHl. apply H3. 
inversion H2. inversion H4. left; constructor... right; intro. apply H6. inversion H7...
right. intro. apply H5. inversion H6...
Qed.

Lemma split_components : forall A B (l : list (A*B)), (split l = (fst (split l), snd (split l))).
induction l. reflexivity. remember a as a'; destruct a'; simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_snd_snd_split : forall A B (l : list (A*B)), map (@snd A B) l = snd (split l).
Proof with eauto.
induction l. reflexivity. unfold map. fold (map (@snd A B) l). rewrite IHl. 
simpl. remember a as a'; destruct a'. simpl. 
rewrite split_components. reflexivity.
Qed.
Lemma map_fst_fst_split : forall A B (l : list (A*B)), map (@fst A B) l =  fst (split l).
Proof with eauto.
induction l. reflexivity. unfold map. fold (map (@fst A B) l). rewrite IHl. 
simpl. remember a as a'; destruct a'. simpl. 
rewrite split_components. reflexivity.
Qed.

Lemma take_while A (l : list A)
  (P : A -> Prop) (dec : forall x, In x l -> decidable (P x)) : 
  (Forall P l) \/ (exists l1 : list A, exists l2 : list A, exists x : A, l = l1 ++ x :: l2 /\ Forall P l1 /\ ~ P x).
Proof with eauto.
  induction l. left; constructor...
  assert (D := forall_dec_dec_forall P (l:=l)).
  assert (Forall P l \/ ~ Forall P l). apply D. unfold decidable in dec. rewrite Forall_forall. intros. apply dec.
  right...
  assert (P a \/ ~ P a). apply dec. left...
  inversion H. inversion H0. left. constructor... right. exists []; exists l; exists a. auto.
  assert (Forall P l \/ exists l1, exists l2, exists x, l = l1 ++ x :: l2 /\ Forall P l1 /\ ~ P x). apply IHl. intros. apply dec.
  right...
  inversion H2. contradiction. clear H2. 
  inversion H0. inversion H3. inversion H4. inversion H5. right. exists (a :: x). exists x0. exists x1. inversion H6. split. rewrite H7... inversion H8. split... 
  right. exists []; exists l; exists a...
Qed.

Lemma forall_fst_comm : forall A B (l : list (A*B)) (P : A -> Prop),
  Forall (fun ab : A*B => P (fst ab)) l -> Forall P (fst (split l)).
Proof with eauto.
  induction l; intros. constructor. remember a as a'; destruct a'. simpl.
  rewrite (split_components l). simpl. inversion H. constructor. auto. apply IHl. auto.
Qed.
Lemma forall_snd_comm : forall A B (l : list (A*B)) (P : B -> Prop),
  Forall (fun ab : A*B => P (snd ab)) l -> Forall P (snd (split l)).
Proof with eauto.
  induction l; intros. constructor. remember a as a'; destruct a'. simpl.
  rewrite (split_components l). simpl. inversion H. constructor. auto. apply IHl. auto.
Qed.

Lemma fst_split_comm : forall A B l1 (ab : A*B) l2, 
  fst (split (l1 ++ ab :: l2)) = fst (split l1) ++ fst ab :: fst (split l2).
Proof with eauto.
  induction l1; intros. destruct ab as (a,b).
  simpl. induction l2; intros. reflexivity.
  destruct a0 as (a0, b0). simpl. rewrite (split_components l2) in *. reflexivity.
  destruct a as (a0, b0). simpl. rewrite (split_components (l1 ++ ab :: l2)). simpl.
  rewrite (split_components l1). simpl. rewrite IHl1. reflexivity.
Qed.
Lemma snd_split_comm : forall A B l1 (ab : A*B) l2, 
  snd (split (l1 ++ ab :: l2)) = snd (split l1) ++ snd ab :: snd (split l2).
Proof with eauto.
  induction l1; intros. destruct ab as (a,b).
  simpl. induction l2; intros. reflexivity.
  destruct a0 as (a0, b0). simpl. rewrite (split_components l2) in *. reflexivity.
  destruct a as (a0, b0). simpl. rewrite (split_components (l1 ++ ab :: l2)). simpl.
  rewrite (split_components l1). simpl. rewrite IHl1. reflexivity.
Qed.

Lemma fst_split_cons : forall A B a b (l : list (A*B)), fst (split ((a, b) :: l)) = a :: fst (split l). 
  intros. simpl. rewrite (split_components l); simpl. reflexivity.
Qed.
Lemma snd_split_cons : forall A B a b (l : list (A*B)), snd (split ((a, b) :: l)) = b :: snd (split l). 
  intros. simpl. rewrite (split_components l); simpl. reflexivity.
Qed.

Lemma fst_split_map_snd : forall A B C (l : list (A*B)) (P : B -> C),
  fst (split (map (fun ab => (fst ab, P (snd ab))) l)) = fst (split l).
Proof with eauto.
  induction l; intros. reflexivity.
  destruct a as (a,b). simpl. 
  rewrite (split_components l). rewrite (split_components (map (fun ab => (fst ab, P (snd ab))) l)). simpl.
  f_equal. apply IHl.
Qed.

Lemma snd_split_map_fst : forall A B C (l : list (A*B)) (P : A -> C),
  snd (split (map (fun ab => (P (fst ab), snd ab)) l)) = snd (split l).
Proof with eauto.
  induction l; intros. reflexivity.
  destruct a as (a,b). simpl. 
  rewrite (split_components l). rewrite (split_components (map (fun ab => (P (fst ab), snd ab)) l)). simpl.
  f_equal. apply IHl.
Qed.


Lemma forall_app : forall A (l1 : list A) l2 P, Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof with eauto.
intros. split. induction l1. simpl... intro. inversion H. split. constructor... apply (IHl1 H3). apply (IHl1 H3).
intros. inversion H. induction l1. simpl... constructor. inversion H0... fold (l1 ++ l2). apply IHl1. split...
inversion H0... inversion H0...
Qed.

Lemma forall_map_comm : forall A B (l : list A) P (f : A -> B), Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof with eauto.
  intros; induction l. simpl. split; intros; constructor.
  split. intros. simpl in H. inversion H. constructor... apply IHl...
  intros. inversion H. simpl. constructor... apply IHl...
Qed.

Lemma Forall_in : forall A (l : list A) (P : A -> Prop) e, Forall P l -> In e l -> P e.
Proof with auto.
intros. induction H. inversion H0.
inversion H0. subst. auto. auto.
Qed.

Lemma in_middle : forall A (l1 : list A) e l2, In e (l1 ++ e :: l2).
intros.
induction l1. simpl; left; auto. simpl. right; auto.
Qed.

Lemma remove_fst_in : forall A B (a : A) (b : B) (l : list (A*B)) eq_dec, ~ In (a,b) (remove_fst a l eq_dec).
Proof with eauto.
  induction l. simpl...
  intros. destruct a0 as (xa, xb). simpl. destruct (eq_dec a xa). apply IHl.
  simpl. intro. inversion H. inversion H0. symmetry in H2; contradiction. apply (IHl eq_dec H0).
Qed.
Lemma remove_fst_in_pair : forall A B a (l : list (A*B)) eq_dec, ~ In a (fst (split (remove_fst a l eq_dec))).
Proof with eauto.
  intros. induction l; simpl... intro. apply IHl. destruct a0 as (aa, ab). destruct (eq_dec a aa); simpl...
  simpl in H. rewrite (split_components (remove_fst a l eq_dec)) in H. simpl in H.
  inversion H. symmetry in H0; contradiction. auto.
Qed.
Lemma still_not_in : forall A B s (l:list(A*B)) eq_dec, ~ In s (map (@fst A B) l) -> ~ In s (map (@fst A B) (remove_fst s l eq_dec)).
Proof with auto. induction l; simpl...
  intros; intro. destruct a as (aa, ab). simpl in *.
  assert (aa <> s /\ ~ In s (map (@fst A B) l)). split. intro; apply H; left... intro; apply H; right...
  clear H. inversion_clear H1. destruct (eq_dec s aa). symmetry in e; contradiction. 
  inversion H0. simpl in H1; contradiction. unfold not in IHl. apply IHl with eq_dec. intro. contradiction. auto.
Qed.
Theorem in_split_fst : forall A B a (l:list (A*B)), In a (fst (split l)) -> exists l1, exists l2, exists b, l = l1++(a,b)::l2.
Proof.
  induction l; intros; simpl... inversion H. destruct a0 as (xa, xb). rewrite fst_split_cons in H.
  inversion H. exists []; exists l; exists xb... subst; simpl; reflexivity.
  clear H. assert (H := IHl H0). inversion_clear H. inversion_clear H1. inversion_clear H. 
  exists ((xa,xb)::x); exists x0; exists x1. subst; simpl. reflexivity.
Qed.

  Lemma remove_app_comm : forall A B l1 (f:A) (x:B) l2 eq_dec, 
    remove_fst f (l1 ++ (f, x) :: l2) eq_dec = remove_fst f l1 eq_dec ++ remove_fst f [(f,x)] eq_dec ++ remove_fst f l2 eq_dec.
    Proof with auto. induction l1. simpl... intros. destruct (eq_dec f f)... intros.
      destruct a as (aa, ab). remember ((f, x) :: l2) as temp. simpl.
      destruct (eq_dec f aa). rewrite Heqtemp; apply IHl1. rewrite <- app_comm_cons.
      f_equal. subst. apply IHl1. 
    Qed.
Lemma fst_split_comm2 : forall A B (l1 : list(A*B)) l2, 
  fst (split (l1 ++ l2)) = fst (split l1) ++ fst (split l2).
Proof with eauto.
  induction l1; intros. simpl...
  simpl.
  destruct a as (a0, b0). rewrite (split_components l1); rewrite (split_components l2); 
  rewrite (split_components (l1 ++ l2)); simpl. f_equal...
Qed.
Lemma not_in_remove_eq : forall A B f (l: list (A*B)) eq_dec, ~ In f (fst (split l)) -> l = remove_fst f l eq_dec.
Proof with eauto.
  induction l. intros. simpl...
  intros. destruct a as (s, e). simpl in H. rewrite (split_components l) in H; simpl in H.
  assert (s <> f). intro; apply H; left... assert (~ In f (fst (split l))). intro; apply H; right...
  clear H. assert (H := IHl eq_dec H1). simpl. destruct (eq_dec f s). symmetry in e0; contradiction.
  f_equal...
Qed.
Lemma snd_split_comm2 : forall A B (l1 : list(A*B)) l2, 
  snd (split (l1 ++ l2)) = snd (split l1) ++ snd (split l2).
Proof with eauto.
  induction l1; intros. simpl...
  simpl.
  destruct a as (a0, b0). rewrite (split_components l1); rewrite (split_components l2); 
  rewrite (split_components (l1 ++ l2)); simpl. f_equal...
Qed.
Lemma update_fieldnames_eq : forall A B (l:list(A*B)) f v eq_dec, map (@fst A B) l = map (@fst A B) (update_assoc l f v eq_dec).
Proof. induction l; intros; auto...
  destruct a as (s,e). simpl. destruct (eq_dec f s); f_equal; simpl. auto. f_equal; apply IHl.
Qed.
Lemma update_values_eq : forall A B l f v P eq_dec, Forall P (map (@snd A B) l) -> P v -> Forall P (map (@snd A B) (update_assoc l f v eq_dec)).
Proof with auto. induction l; intros; simpl; auto. intros.
  destruct a as (s, e). destruct (eq_dec f s). simpl. constructor... inversion H...
  constructor. inversion H... simpl in H. apply IHl. inversion H... auto.
Qed.
