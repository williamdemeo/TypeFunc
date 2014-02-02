(** The dual Frobenius rule.
    From Andrej Bauer's YouTube tutorial:
    http://www.youtube.com/watch?v=tZRAFKIv6Js&feature=share&list=PLDD40A96C2ED54E99&index=4

    firstorder doesn't work because implication from left to right requires lem.
*)
Definition lem := forall p, p \/ ~p.
Definition frobenius := forall (A : Set) (p : A -> Prop) (q : Prop),
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).


Theorem frobenius_to_lem: frobenius -> lem.
Proof.
  unfold frobenius, lem.
  firstorder.
  destruct (H {_ : unit | p} (fun _ => False) p).   (* {_ : unit | p} is empty if p false *)
  clear H1.
  rename H0 into G.
  cut (p \/ (sig (fun _ : unit => p) -> False)).    (* insert an intermediate step *)

  (** Coq splits into subgoals: prove intermediate thing implies end goal then prove intermediate thing.
      Also note (sig (fun _ : unit => p)) is Coq's way of representing the set {_ : unit | p} 
      Coq turned the antecedent of the result of our destruct statement 
          destruct (H {_ : unit | p} (fun _ => False) p). 
      into the implication
          (sig (fun _ : unit => p) -> p \/ False)
      because we have a forall where we are quantifying over a set and then the statement being quantified does not depend on the variable.
  *)
  intros [K1 | K2].   (* two branches of the disjunction *)
  left; assumption.
  right.
  intro.
  apply K2.
  exists tt.
  assumption.
  (* Now we must prove the intermediate step, which is the consequent of G, so... *)
  apply G.
  (* ...and the resulting subgoal is to prove the antecendent of G. *)
  intros [u J].
  left; assumption.
Qed.  


(* sig (fun _ : unit => p) is the set of all elements of type unit which satisfy p. *)


(* How to interpret the mixing of types: Set -> Prop *)
Parameter S : Set.
Parameter q r: Prop.
Lemma map_set_to_prop : forall x : S, q.  
(** Results in S -> q, where equate q with the set of all proofs of q.
    So by S -> q, Coq is saying, 
    "Give me a function that takes elements of S into proofs of q."
 *)

(** Implication is a special case of for all. *)
Lemma map_proofs_to_prop : forall u : q, r.    
(** Says "for all proofs u of p, I can produce a proof of r." 
    This is the same as q -> r. *)

(* You could also write this as *)
Lemma map_proofs_to_prop2 : forall _ : q, r.    

Definition A := {y : S | q}.  (* the set of all elements of type S that satisfy q *)

Print A.
