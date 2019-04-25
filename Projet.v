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
| verifLeft : forall (n l : nat) (left right : Abin), (isNode left l) -> (isNode (Node n left right) n)
| verifRight : forall (n r : nat) (left right : Abin), (isNode right r) -> (isNode (Node n left right) n).

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
intros. inversion H. auto. auto. auto.
apply min_n.
intros. inversion H. auto. auto. auto.
apply verifNodeABR. apply verifNodeABR.
apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty.
apply min_Empty.
apply verifNodeABR. apply verifEmptyABR. apply verifEmptyABR.
apply max_Empty.
apply min_Empty.
apply max_n.
intros. inversion H. auto. auto . auto.
apply min_n.
intros. inversion H. auto. auto. auto. 
apply max_n.
intros. inversion H. auto. auto. auto.
apply min_n.
intros. inversion H. auto. auto. auto.
Qed.

Ltac tactique_isABR :=
repeat (auto ||
 match goal with
| |- isABR Empty => apply verifEmptyABR
| |- isABR (Node ?n Empty Empty) => apply verifLeafABR
| |- isABR (Node ?n ?l ?r) => apply verifNodeABR
| |- isMax Empty ?n => apply max_Empty
| |- isMin Empty ?n => apply min_Empty
| |- isMax (Node ?n ?m ?o) ?p => apply max_n; intros
| |- isMin (Node ?n ?m ?o) ?p => apply min_n; intros
| H : isNode (Node ?w ?x ?y) ?z |- _ => inversion H; clear H
end).

Lemma testTac_isABR : (isABR (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 8 (Node 6 Empty Empty) (Node 11 Empty Empty)))).
tactique_isABR.

Lemma test_isntABR : ~(isABR (Node 5 (Node 3 Empty Empty) (Node 4 Empty Empty))).
(**)

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


Functional Scheme searchABRInd := Induction for search Sort Prop.
Functional Scheme insertABRInd := Induction for insert Sort Prop.
Functional Scheme supprABRInd := Induction for suppr Sort Prop.

(* --- PREUVES --- *)
Lemma proof_search : forall (a : Abin) (n: nat), (isABR a) -> (isNode a n) -> (search a n).
(*intros.
induction a.
simpl.
inversion H0.
simpl.
elim (Nat.eq_dec n n0); elim (lt_dec n n0);intros; auto.
apply IHa1.
inversion H.
tactique_isABR.
apply H5.
*)

Lemma proof_insert : forall (a : Abin) (n: nat), (isABR a) -> (isABR (insert a n)).
intros.
elim H; intros.
simpl.
tactique_isABR.
simpl.
elim (Nat.eq_dec n n0); elim (lt_dec n n0);intros.
tactique_isABR.
rewrite <- a1.
rewrite <- H1.
auto.
rewrite <- a1.
rewrite <- H2.
auto.
rewrite <- a1.
rewrite <- H2.
auto.

tactique_isABR.
rewrite <- a0.
rewrite <- H1.
auto.
rewrite <- a0.
rewrite <- H2.
auto.
rewrite <- a0.
rewrite <- H2.
auto.

tactique_isABR.
rewrite <- H1.
auto.
rewrite <- a0.
rewrite <- H2.
auto.
rewrite <- a0.
rewrite <- H2.
auto.

(* Search : 
Insert : inserer un element , element d'avant sont encore dans l'arbre, arbre d'avant + element et rien d'autre
suppr : supprime bien un element , ....*)