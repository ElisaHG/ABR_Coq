Require Import Nat.
Require Import FunInd.
Require Export ZArith. 
Require Import Classical.

(* --- Arbre Binaire --- *)
Inductive Abin : Set :=
| Empty : Abin
| Node : nat -> Abin -> Abin -> Abin.

Compute (Node 5 (Node 6 Empty Empty) (Node 7 (Node 8 Empty Empty) Empty)).  (* exemple d'arbre binaire *)

(*--------- Fonctions supplementaires qui utilisent les Arbres binaires -------------*)
(* --- Taille Arbre Binaire --- *)
Fixpoint HeightAbin (tree : Abin) : nat :=
match tree with
| Empty => 0
| (Node n Empty Empty)  => 1
| (Node n l r) => 1 + (max (HeightAbin l) (HeightAbin r))
end.

(* --- nombre de noeuds dans Arbre Binaire --- *)
Fixpoint nbNodeAbin (tree : Abin) : nat :=
match tree with
| Empty => 0
| (Node n Empty Empty)  => 1
| (Node n l r) => 1 + (nbNodeAbin l) + (nbNodeAbin r)
end.

Compute (HeightAbin (Node 5 (Node 6 Empty Empty) (Node 7 (Node 8 Empty Empty) Empty))). (* arbre binaire de taille 3 *)
Compute (nbNodeAbin (Node 5 (Node 6 Empty Empty) (Node 7 (Node 8 Empty Empty) Empty))). (* arbre binaire avec 4 noeuds *)
(*-----------------------------------------------------------------------------------------------------*)

(* --- Noeud --- *)
Inductive isNode : Abin -> nat -> Prop :=
| verifCurrentNode : forall (n:nat) (left right : Abin), (isNode (Node n left right) n)
| verifLeft : forall (n m : nat) (left right : Abin), (isNode left m) -> (isNode (Node n left right) m)
| verifRight : forall (n m : nat) (left right : Abin), (isNode right m) -> (isNode (Node n left right) m).

(* --- Feuille --- *)
Inductive isLeaf : Abin -> Prop :=
verifLeaf : forall (n : nat), (isLeaf (Node n Empty Empty)).

(* --- Etre le max/min dans un arbre --- *)
Inductive isMax : Abin -> nat -> Prop :=
| max_Empty : forall (x : nat), (isMax Empty x)
| max_n : forall (x : nat) (node : Abin), (forall (n : nat), (isNode node n) -> (n <= x)) -> (isMax node x).

Inductive isMin : Abin -> nat -> Prop :=
| min_Empty : forall (n : nat), (isMin Empty n)
| min_n : forall (x:nat) (node : Abin), (forall (n : nat), (isNode node n) -> (n > x)) -> (isMin node x).

(* --- Etre un ABR --- *)
Inductive isABR : Abin -> Prop :=
| verifEmptyABR : (isABR Empty)
| verifLeafABR : forall (n : nat),  (isABR (Node n Empty Empty))
| verifNodeABR : forall (n : nat) (left right : Abin), (isABR right) -> (isABR left) 
  -> (isMax left n) -> (isMin right n) -> (isABR (Node n left right)).

Lemma test_isABR : (isABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))).
apply verifNodeABR. apply verifNodeABR. apply verifNodeABR.
apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty. apply min_Empty.
apply verifNodeABR. apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty. apply min_Empty.
apply max_n.
intros. inversion H. auto.
inversion H4. inversion H4.
apply min_n.
intros. inversion H. auto.
inversion H4. inversion H4.
apply verifNodeABR. apply verifNodeABR.
apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty. apply min_Empty.
apply verifNodeABR. apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty. apply min_Empty.
apply max_n.
intros. inversion H. auto.
inversion H4. inversion H4.
apply min_n.
intros. inversion H. auto.
inversion H4. inversion H4.
apply max_n.
intros. inversion H. auto.
inversion H4. inversion H4.
auto. auto. auto.
inversion H4. inversion H4.
auto. auto. auto.
inversion H4. inversion H4.
auto. auto. auto.
inversion H19. inversion H9. inversion H9. inversion H9.
inversion H4. auto. inversion H9. inversion H9.
apply min_n.
intros. inversion H. auto.
inversion H4. auto. inversion H9. inversion H9. inversion H4. omega.
inversion H9. inversion H9.

Ltac tactique_isABR :=
repeat (auto || omega ||
 match goal with
| |- isABR Empty => apply verifEmptyABR
| |- isABR (Node ?n Empty Empty) => apply verifLeafABR
| |- isABR (Node ?n ?l ?r) => apply verifNodeABR
| |- isMax Empty ?n => apply max_Empty
| |- isMin Empty ?n => apply min_Empty
| |- isMax (Node ?n ?m ?o) ?p => apply max_n; intros
| |- isMin (Node ?n ?m ?o) ?p => apply min_n; intros
| H : isNode (Node ?w ?x ?y) ?z |- _ => inversion H; clear H
| H : isNode (Node ?z Empty Empty) ?n|-  ?n > ?y => inversion H; clear H
| H : isNode (Node ?z Empty Empty) ?n|-  ?n < ?y => inversion H;clear H
| H : isNode (Node ?z Empty Empty) ?n|-  ?n >= ?y => inversion H; clear H
| H : isNode (Node ?z Empty Empty) ?n|-  ?n <= ?y => inversion H; clear H
| H : isNode Empty ?n|- ?n > ?y => inversion H; clear H
| H : isNode Empty ?n|- ?n >= ?y => inversion H; clear H
| H : isNode Empty ?n|- ?n < ?y => inversion H; clear H
| H : isNode Empty ?n|- ?n <= ?y => inversion H; clear H
end).

Lemma testTac_isABR : (isABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))).
tactique_isABR.
Qed.

(* --- Fonction de recherche d'un element dans un ABR --- *)
Fixpoint search (arb : Abin) (x : nat) : Prop :=
match arb with
| Empty => False
| (Node n l r) => 
  match (Nat.eq_dec x n) with
    | left _ => True
    | right _ => 
      match (lt_dec x n) with
        | left _ => (search l x)
        | right _ => (search r x)
       end
    end
end.

Compute (search (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 3). (* 3 present dans l'arbre *)
Compute (search (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 10).  (* 10 absent de l'arbre *)

(* --- Fonction d'insertion d'un element dans un ABR --- *)
Fixpoint insert (arb : Abin) (x : nat) : Abin :=
match arb with
| Empty => (Node x Empty Empty)
| (Node n l r) => 
  match (Nat.eq_dec x n) with
    | left _ => (Node n (insert l x) r)
    | right _ => 
      match (lt_dec x n) with
        | left _ => (Node n (insert l x) r)
        | right _ => (Node n l (insert r x))
       end
    end
end.

Compute (insert (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 14).
Compute (insert (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 6).

(* --- trouver le max/min dans un ABR (utile pour fonction de suppression) --- *)
Fixpoint searchMaxABR (arb : Abin) : Abin :=
match arb with
| Empty => Empty
| (Node n l Empty) => (Node n l Empty)
| (Node n l r) => (searchMaxABR r)
end.

Fixpoint searchMinABR (arb : Abin) : Abin :=
match arb with
| Empty => Empty
| (Node n Empty r) => (Node n Empty r)
| (Node n l r) => (searchMinABR l)
end.

(* --- Fonction de suppression d'un element dans un ABR --- *)
Fixpoint suppr (arb : Abin) (x : nat) : Abin :=
match arb with
| Empty => Empty
| (Node n l r) => 
  match (Nat.eq_dec x n) with
    | left _ => 
      match (searchMinABR r) with
         | (Node x a b) => (Node x l (suppr r x))
         | Empty => 
            match (searchMaxABR l) with
              | Empty => Empty
              | (Node x a b) => ( Node x (suppr l x) r)
            end
       end
    | right _ => 
      match (lt_dec x n) with
        | left _ => (Node n (suppr l x) r)
        | right _ => (Node n l (suppr r x))
        end
  end
end.

Compute (searchMaxABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))). (* max = 11 *)
Compute (searchMinABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))). (* min = 2 *)
Compute (suppr (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 5).
Compute (suppr (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 3).
Compute (suppr (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 8).



Functional Scheme searchInductive := Induction for search Sort Prop.
Functional Scheme insertInductive := Induction for insert Sort Prop.
Functional Scheme supprInductive := Induction for suppr Sort Prop.

(* --- PREUVES --- *)
(* si on trouve n dans l'arbre alors n est un noeud de l'arbre *)
Lemma search_correction : forall (a : Abin) (n: nat), (search a n) -> (isNode a n).
intro.
intro.
functional induction (search a n) using searchInductive;intros.
inversion H.
apply verifCurrentNode.
apply verifLeft.
auto.
apply verifRight.
auto.

(* quand on insere un noeud dans un arbre, n a bien la propriete de noeud *)
Lemma is_node_insert : forall (n : nat) (a : Abin), (isNode (insert a n) n).
intro. intro.
functional induction (insert a n) using insertInductive;intros.
apply verifCurrentNode.
apply verifLeft. apply IHa0.
apply verifLeft. apply IHa0.
apply verifRight. apply IHa0.

Lemma insert_missing_correction : forall (n m : nat) (a: Abin), (isNode (insert a n) m) -> (n <>m) -> (isNode a m).
intro. intro. intro.
functional induction (insert a n) using insertInductive;intros.
inversion H. omega.
apply H5. apply H5.
inversion H. omega.
apply verifLeft. apply IHa0. apply H5. apply H0.
apply verifRight.
assumption.
inversion H; subst.
apply verifCurrentNode.
apply verifLeft. apply IHa0. apply H5. apply H0.
apply verifRight. apply H5.
inversion H; subst.
apply verifCurrentNode.
apply verifLeft. apply H5.
apply verifRight. apply IHa0. apply H5. apply H0.

(* si m est un noeud de l'arbre , m est un noeud de l'arbre auquel on a ajoute un nouveau noeud n *)
Lemma insert_missing_completude : forall (n m : nat) (a: Abin), (isNode a m) -> (isNode (insert a n) m).
intros.
elim H; intros.
simpl.
elim (Nat.eq_dec n n0); elim (lt_dec n n0);intros.
apply verifCurrentNode.
apply verifCurrentNode.
apply verifCurrentNode.
apply verifCurrentNode.
simpl.
elim (Nat.eq_dec n n0); elim (lt_dec n n0);intros.
apply verifLeft. apply H1.
apply verifLeft. apply H1.
apply verifLeft. apply H1.
apply verifLeft. apply H0.
simpl.
elim (Nat.eq_dec n n0); elim (lt_dec n n0);intros.
apply verifRight. apply H0.
apply verifRight. apply H0.
apply verifRight. apply H0.
apply verifRight. apply H1.


(* --------- Idees de preuves non abouties --------- *)
(* Si n est un noeud de l'arbre, on pourra trouver n dans l'arbre *)
Lemma search_completude : forall (a: Abin) (n:nat), (isABR a) -> (isNode a n) -> (search a n).

Lemma insert_unexpected_correction : forall (n m : nat) (a : Abin), (~(isNode (insert a n) m)) -> (n <>m) -> ~(isNode a m).
Lemma insert_unexpected_completude : forall (n m : nat) (a : Abin), ~(isNode a m) -> ~(isNode (insert a n) m).

(* Inserer une valeur plus petite que le max de l'arbre ne modifie pas le max *)
Lemma insert_left_correction : forall (n m : nat) (a : Abin), (isMax (insert a n) m) -> (isMax a m). 
Lemma insert_left_completude : forall (n m : nat) (a : Abin), (isMax a m) -> (n < m) -> (isMax (insert a n) m).
(* Inserer une valeur plus grande que le min de l'arbre ne modifie pas le min *)
Lemma insert_right_correction : forall (n m : nat) (a : Abin), (isMin (insert a n) m) -> (isMin a m).
Lemma insert_right_completude : forall (n m : nat) (a : Abin), (isMin a m) -> (n > m) -> (isMin (insert a n) m).

(* Inserer un noeud dans un ABR conserve la propriete d'ABR *)
Lemma insert_is_abr_corr : forall (n : nat) (a : Abin), (isABR (insert a n)) -> (isABR a).
Lemma insert_is_abr_compl : forall (n : nat) (a : Abin), (isABR a) -> (isABR (insert a n)).




