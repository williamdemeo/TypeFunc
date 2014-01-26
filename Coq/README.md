# First steps with Proof General on Ubuntu 13.10

## Installing Coq and the Proof General/Emacs IDE
In Ubuntu Coq and Proof General are easily installed 
with the Synaptic package manager.

## Andrej Bauer's YouTube tutorial
Andrej Bauer provides a series of short YouTube tutorials.
For example, in [How to use Coq with Proof General][], he shows how to use Coq
to prove that Pierce's law is equivalent to the Law of Excluded Middle.  

Here is a rough transcript of the commands used:

1.  Open a file in emacs called pierce_lem.v  Proof General should automatically
load. 

2.  Enter the first line as follows:
   
        Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.
	   
	then type C-c C-n.  
	
	If you want to go back and change lines, you must type C-c C-u.

3.  Enter the second line as follows:

        Definition lem := forall (p : Prop), p \/ ~ p.

	and type C-c C-n.  If you have typed a bunch of lines and want to evaluate
	everything up to the current point, type C-c C-Enter.

4.  Enter the third and fourth lines as follows:

        Theorem pierce_equiv_lem : pierce <-> lem.
		Proof.
	
	typing C-c C-n after each.
	
5.  The first line of the proof can't be `firstorder.`  You must first unfold
    the definitions, as follows:
	
	    unfold pierce, lem.
		firstorder.


[How to use Coq with Proof General]: http://youtu.be/l6zqLJQCnzo
