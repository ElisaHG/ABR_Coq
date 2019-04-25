Require Import Nat.
Require Import FunInd.
Require Export ZArith. 
Open Scope list.
Require Export List.
Import ListNotations.

(* --- Arbre Binaire --- *)
Inductive Abin : Set :=
| Empty : Abin
| Node : nat -> Abin -> Abin -> Abin.

Compute (Node 5 (Node 6 Empty Empty) (Node 7 (Node 8 Empty Empty) Empty)).

(*--------- Fonctions supplementaires qui utilisent les Arbres binaire --------------*)
Fixpoint HeightAbin (tree : Abin) : nat :=
match tree with
| Empty => 0
| (Node n Empty Empty)  => 1
| (Node n l r) => 1 + (max (HeightAbin l) (HeightAbin r))
end.

Fixpoint nbNodeAbin (tree : Abin) : nat :=
match tree with
| Empty => 0
| (Node n Empty Empty)  => 1
| (Node n l r) => 1 + (nbNodeAbin l) + (nbNodeAbin r)
end.

Compute (HeightAbin (Node 5 (Node 6 Empty Empty) (Node 7 (Node 8 Empty Empty) Empty))).
Compute (nbNodeAbin (Node 5 (Node 6 Empty Empty) (Node 7 (Node 8 Empty Empty) Empty))).
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
apply max_Empty.
apply min_Empty.
apply verifNodeABR. apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty.
apply min_Empty.
apply max_n.
intros. inversion H. auto.
inversion H4. inversion H4.
apply min_n.
intros. inversion H. auto.
inversion H4. inversion H4.
apply verifNodeABR. apply verifNodeABR.
apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty.
apply min_Empty.
apply verifNodeABR. apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty.
apply min_Empty.
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
Qed.

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

(*Lemma test_isntABR : ~(isABR (Node 5 (Node 3 Empty Empty) (Node 4 Empty Empty))).*)

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

Compute (search (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 3).
Compute (search (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 10).

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

Compute (searchMaxABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))).
Compute (searchMinABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))).
Compute (suppr (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 5).
Compute (suppr (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 3).
Compute (suppr (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty))) 8).


Functional Scheme searchInductive := Induction for search Sort Prop.
Functional Scheme insertInductive := Induction for insert Sort Prop.
Functional Scheme supprInductive := Induction for suppr Sort Prop.

(* --- PREUVES --- *)
Lemma proof_search_correction : forall (a : Abin) (n: nat), (search a n) -> (isNode a n).
intro.
intro.
functional induction (search a n) using searchInductive;intros.
inversion H.
apply verifCurrentNode.
apply verifLeft with x.


Lemma proof_search_completude : forall (a: Abin) (n:nat), (isABR a) -> (isNode a n) -> (search a n).

Lemma proof_insert_is_node : forall (n : nat) (a : Abin), (isNode (insert a n) n).

Lemma proof_insert_missing_correction : forall (n m : nat) (a: Abin), ((n <>m) /\ (isNode (insert a n) m)) -> (isNode a m).

Lemma proof_insert_missing_completude : forall (n m : nat) (a: Abin), (isNode a m) -> (isNode (insert a n) m).

Lemma proof_insert_unexpected_correction : forall (n m : nat) (a : Abin), ((n <>m) /\ ~(isNode (insert a n) m)) -> ~(isNode a m).

Lemma proof_insert_unexpected_completude : forall (n m : nat) (a : Abin), ~(isNode a m) -> ~(isNode (insert a n) m).

Lemma insert_left_abr_correction : forall (n m : nat) (left : Abin), ((n < m) /\ (isMax (insert left n) m)) -> (isMax left m).

Lemma insert_left_abr_completude : forall (n m : nat) (left : Abin),  (isMax left m) -> (isMax (insert left n) m).

Lemma insert_right_abr_correction : forall (n m : nat) (right : Abin), ((n > m) /\ (isMin (insert right n) m)) -> (isMin right m).

Lemma insert_right_abr_completude : forall (n m : nat) (right : Abin), (isMin right m) -> (isMin (insert right n) m).

Lemma insert_is_abr_correction : forall (n : nat) (a : Abin), (isABR (insert a n)) -> (isABR a).

Lemma insert_is_abr_completude : forall (n : nat) (a : Abin), (isABR a) -> (isABR (insert a n)).



