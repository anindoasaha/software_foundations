# Software Foundations

# Logical Foundations
## Preface
> Topics in the series include basic concepts of logic, computer-assisted theorem proving, the Coq proof assistant, functional programming, operational semantics, logics for reasoning about programs, and static type systems


> This book, Logical Foundations, lays groundwork for the others, introducing the reader to the basic ideas of functional programming, constructive logic, and the Coq proof assistant.

**Logic**

> Logic is the field of study whose subject matter is proofs — unassailable arguments for the truth of particular propositions.

**Proof Assistants**

- *Automated theorem provers* provide "push-button" operation: you give them a proposition and they return either *true* or *false* (or, sometimes, *don't know: ran out of time*).
- *Proof assistants* are hybrid tools that automate the more routine aspects of building proofs while depending on human guidance for more difficult aspects. Widely used proof assistants include Isabelle, Agda, Twelf, ACL2, PVS, and **Coq**, among many others.

$$$$
**Coq**

- As a *platform for modeling programming languages*
  - describe and reason about complex language definitions
- As an *environment for developing formally certified software and hardware*
  - CompCert, a fully-verified optimizing compiler for C.
  - for proving the correctness of subtle algorithms involving floating point numbers.
  - CertiKos, a fully verified hypervisor.
  - verified implementations of the open-source RISC-V processor.
- As a *realistic environment for functional programming with dependent types*
- As a *proof assistant for higher-order logic*
  - validate a number of important results in mathematics.
  - first formally verified proof of the 4-color theorem
  - formalization of the Feit-Thompson Theorem.


> In French, 'coq' means rooster, and it sounds like the initials of the Calculus of Constructions (CoC) on which it is based." The rooster is also the national symbol of France, and C-o-q are the first three letters of the name of Thierry Coquand, one of Coq's early developers.

 
**Functional Programming**

> collection of programming idioms that can be used in almost any programming language and to a family of programming languages designed to emphasize these idioms.


> its roots go back to Church's lambda-calculus.


> as much as possible, computation should be pure, - only effect of execution should be to produce a result: -  free from side effects such as I/O, assignments to mutable variables, redirecting pointers, etc. 


> If every operation on a data structure yields a new data structure, leaving the old one intact, then there is no need to worry about how that structure is being shared .


> These considerations are particularly critical in concurrent systems, where every piece of mutable state that is shared between threads is a potential source of pernicious bugs. 


> Coq itself can be viewed as a combination of a small but extremely expressive functional programming language plus a set of tools for stating and proving logical assertions. 


> proofs are programs.

**Practicalities**


- Dependencies


![Chapter dependencies](https://d2mxuefqeaa7sj.cloudfront.net/s_C277435B735E073A5F34BC0CF5AC19A3A77DC422EB3CE96F6D397078D33AC471_1507408151657_deps.gif)



- **System Requirements**


> A current installation of Coq, available from the Coq home page. These files have been tested with Coq 8.6.


> Proof General is an Emacs-based IDE. It tends to be preferred by users who are already comfortable with Emacs. It requires a separate installation (google "Proof General").

**Exercises**

  - One star: easy exercises that underscore points in the text and that, for most readers, should take only a minute or two. Get in the habit of working these as you reach them.
  - Two stars: straightforward exercises (five or ten minutes).
  - Three stars: exercises requiring a bit of thought (ten minutes to half an hour).
  - Four and five stars: more difficult exercises (half an hour and up).

**Downloading the Coq Files**
http://www.cis.upenn.edu/~bcpierce/sf

**Lecture Videos**
https://deepspec.org/event/dsss17/coq_intensive.html


----------
## Functional Programming in Coq (Basics)

**Introduction**

> If a procedure or method has no side effects, then (ignoring efficiency) all we need to understand about it is how it maps inputs to outputs. 


> emphasizes the use of functions (or methods) as first-class values — i.e., values that can be passed as arguments to other functions, returned as results, included in data structures, etc. 


> algebraic data types and pattern matching, which make it easy to construct and manipulate rich data structures, and sophisticated polymorphic type systems supporting abstraction and code reuse.

 

> Coq offers all of these features.


> The first half of this chapter introduces the most essential elements of Coq's functional programming language, called Gallina. 
> The second half introduces some basic tactics that can be used to prove properties of Coq programs.

**Data and Functions**

**Enumerated Types**

Days of the Week


    Inductive day : Type :=
      | monday : day
      | tuesday : day
      | wednesday : day
      | thursday : day
      | friday : day
      | saturday : day
      | sunday : day.

The type is called day, and its members are monday, tuesday, etc. The second and following lines of the definition can be read "monday is a day, tuesday is a day, etc."

Having defined day, we can write functions that operate on days.


    Definition next_weekday (d:day) : day :=
      match d with
      | monday ⇒ tuesday
      | tuesday ⇒ wednesday
      | wednesday ⇒ thursday
      | thursday ⇒ friday
      | friday ⇒ monday
      | saturday ⇒ monday
      | sunday ⇒ monday
      end.


> Coq can often figure out these types for itself when they are not given explicitly — i.e., it can do type inference — but we'll generally include them to make reading easier.

First, we can use the command **Compute** to evaluate a compound expression involving next_weekday.


    Compute (next_weekday friday).
    (* ==> monday : day *)


    Compute (next_weekday (next_weekday saturday)).
    (* ==> tuesday : day *)

Second, we can record what we *expect* the result to be in the form of a Coq **example**:


    Example test_next_weekday:
      (next_weekday (next_weekday saturday)) = tuesday.


    Proof. simpl. reflexivity. Qed.


> this can be read as "The assertion we've just made can be proved by observing that both sides of the equality evaluate to the same thing, after some simplification."

Third, we can ask Coq to ***extract***, from our **Definition**, a program in some other, more conventional, programming language (OCaml, Scheme, or Haskell) with a high-performance compiler.

**Booleans**


    Inductive bool : Type :=
      | true : bool
      | false : bool.


> Coq does, of course, provide a default implementation of the booleans, together with a multitude of useful functions and lemmas. (Take a look at Coq.Init.Datatypes in the Coq library documentation if you're interested.)

Functions over booleans can be defined in the same way as above:


    Definition negb (b:bool) : bool :=
      match b with
      | true ⇒ false
      | false ⇒ true
      end.
      
      Definition andb (b1:bool) (b2:bool) : bool :=
      match b1 with
      | true ⇒ b2
      | false ⇒ false
      end.
      
      Definition orb (b1:bool) (b2:bool) : bool :=
      match b1 with
      | true ⇒ true
      | false ⇒ b2
      end.

The last two of these illustrate Coq's syntax for multi-argument function definitions.


    Example test_orb1: (orb true false) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_orb2: (orb false false) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_orb3: (orb false true) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_orb4: (orb true true) = true.
    Proof. simpl. reflexivity. Qed.

The Notation command defines a new symbolic notation for an existing definition.


    Notation "x && y" := (andb x y).
    Notation "x || y" := (orb x y).
    
    Example test_orb5: false || false || true = true.
    Proof. simpl. reflexivity. Qed.

**Function Types**

 The Check command asks Coq to print the type of an expression.
 

    Check true.
    (* ===> true : bool *)
    Check (negb true).
    (* ===> negb true : bool *)
    
    Check negb.
    (* ===> negb : bool -> bool *)

The type of negb, written **bool → bool** and pronounced **"bool arrow bool,"** can be read, "Given an input of type bool, this function produces an output of type bool." Similarly, the type of andb, written **bool → bool → bool**, can be read, "Given two inputs, both of type bool, this function produces an output of type bool."

**Compound Types**


    Inductive rgb : Type :=
      | red : rgb
      | green : rgb
      | blue : rgb.
      
    Inductive color : Type :=
      | black : color
      | white : color
      | primary : rgb → color.


> if p is an expression belonging to the set rgb, then primary p (pronounced "the constructor primary applied to the argument p") is an expression belonging to the set color


> We can define functions on colors using pattern matching.


    Definition monochrome (c : color) : bool :=
      match c with
      | black ⇒ true
      | white ⇒ true
      | primary p ⇒ false
      end.


>  a pattern matching **primary** should include either a variable (as above) or a constant of appropriate type (as below)


    Definition isred (c : color) : bool :=
      match c with
      | black ⇒ false
      | white ⇒ false
      | primary red ⇒ true
      | primary _ ⇒ false
      end.

**Modules**

> If we enclose a collection of declarations between Module X and End X markers, then, in the remainder of the file after the End, these definitions are referred to by names like X.foo instead of just foo. 


    Module NatPlayground.

**Numbers**


> allow its constructors to take arguments from the very same type — that is, to allow the rules describing its elements to be inductive


- define (a unary representation of) natural numbers
    Inductive nat : Type :=
      | O : nat
      | S : nat → nat.


- O and S are constructors;
- the expression O belongs to the set nat;
- if n is an expression belonging to the set **nat**, then S n is also an expression belonging to the set **nat**; and
- expressions formed in these two ways are the only ones belonging to the set **nat**.

 The predecessor function:

    Definition pred (n : nat) : nat :=
      match n with
        | O ⇒ O
        | S n' ⇒ n'
      end.

 

    End NatPlayground.


> Coq provides a tiny bit of built-in magic for parsing and printing them: ordinary arabic numerals can be used as an alternative to the "unary" notation defined by the constructors S and O. Coq prints numbers in arabic form by default:


    Check (S (S (S (S O)))).
      (* ===> 4 : nat *)
      
    Definition minustwo (n : nat) : nat :=
      match n with
        | O ⇒ O
        | S O ⇒ O
        | S (S n') ⇒ n'
      end.
      
    Compute (minustwo 4).
      (* ===> 2 : nat *)
    
    Check S.
    Check pred.
    Check minustwo.

There is a fundamental difference between the first one and the other two: functions like pred and minustwo come with ***computation rules*** — e.g., the definition of pred says that pred 2 can be simplified to 1 — while the **definition of S has no such behavior attached**. 

For most function definitions over numbers, just pattern matching is not enough: we also need recursion.

 To write such functions, we use the keyword Fixpoint.

    Fixpoint evenb (n:nat) : bool :=
      match n with
      | O ⇒ true
      | S O ⇒ false
      | S (S n') ⇒ evenb n'
      end.


    Definition oddb (n:nat) : bool := negb (evenb n).


    Example test_oddb1: oddb 1 = true.
    Proof. simpl. reflexivity. Qed.
    Example test_oddb2: oddb 4 = false.
    Proof. simpl. reflexivity. Qed.

*(You will notice if you step through these proofs that simpl actually has no effect on the goal — all of the work is done by reflexivity. We'll see more about why that is shortly.)*

(n m : nat) means just the same as if we had written (n : nat) (m : nat).


    Module NatPlayground2.
    
    Fixpoint plus (n : nat) (m : nat) : nat :=
      match n with
        | O ⇒ m
        | S n' ⇒ S (plus n' m)
      end.


    Fixpoint mult (n m : nat) : nat :=
      match n with
        | O ⇒ O
        | S n' ⇒ plus m (mult n' m)
      end.
      
    Example test_mult1: (mult 3 3) = 9.
    Proof. simpl. reflexivity. Qed.

You can match two expressions at once by putting a comma between them:


    Fixpoint minus (n m:nat) : nat :=
      match (n, m) with
      | (O , _) ⇒ O
      | (S _ , O) ⇒ n
      | (S n', S m') ⇒ minus n' m'
      end.


    End NatPlayground2.


- base^power:
    Fixpoint exp (base power : nat) : nat :=
      match power with
        | O ⇒ S O
        | S p ⇒ mult base (exp base p)
      end.



- Test for equality:
    Fixpoint beq_nat (n m : nat) : bool :=
      match n with
      | O ⇒ match m with
             | O ⇒ true
             | S m' ⇒ false
             end
      | S n' ⇒ match m with
                | O ⇒ false
                | S m' ⇒ beq_nat n' m'
                end
      end.


- Test if n <= m:
    Fixpoint leb (n m : nat) : bool :=
      match n with
      | O ⇒ true
      | S n' ⇒
          match m with
          | O ⇒ false
          | S m' ⇒ leb n' m'
          end
      end.


    Example test_leb1: (leb 2 2) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_leb2: (leb 2 4) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_leb3: (leb 4 2) = false.
    Proof. simpl. reflexivity. Qed.


## Proof by Simplification
> use **simpl** to simplify both sides of the equation, then use reflexivity to check that both sides contain identical values.


    Theorem plus_O_n : ∀ n : nat, 0 + n = n.
    Proof.
      intros n. simpl. reflexivity. Qed.


> **reflexivity** can perform some simplification automatically when checking that two sides are equal; **simpl** was just added so that we could see the intermediate state — after simplification but before finishing the proof.


    Theorem plus_O_n' : ∀ n : nat, 0 + n = n.
    Proof.
      intros n. reflexivity. Qed.


> **reflexivity** tries "unfolding" defined terms, replacing them with their right-hand sides. The reason for this difference is that, if **reflexivity** succeeds, the whole goal is finished and we don't need to look at whatever expanded expressions reflexivity has created by all this simplification and unfolding; by contrast, **simpl** is used in situations where we may have to read and understand the new goal that it creates.


>  the keywords Example and Theorem (and a few others, including Lemma, Fact, and Remark) mean pretty much the same thing to Coq.


- We've added the quantifier **∀ n:nat**, so that our theorem talks about *all* natural numbers n.


-  Informally, to prove theorems of this form, we generally start by saying "Suppose n is some number..." Formally, this is achieved in the proof by **intros n**, which **moves n from the quantifier in the goal to a** ***context*** **of current assumptions**.


> The keywords **intros, simpl, and reflexivity** are examples of tactics. A tactic is a command that is used between Proof and Qed to guide the process of checking some claim we are making.


    Theorem plus_1_l : ∀ n:nat, 1 + n = S n.
    Proof.
      intros n. reflexivity. Qed.
      
    Theorem mult_0_l : ∀ n:nat, 0 * n = 0.
    Proof.
      intros n. reflexivity. Qed.

*(The _l suffix in the names of these theorems is pronounced "on the left.")*

## Proof by Rewriting

Instead of making a universal claim about all numbers **n** and **m**, it talks about a more specialized property that only holds when **n = m**. The arrow symbol is pronounced "**implies**."


    Theorem plus_id_example : ∀ n m:nat, n = m →
      n + n = m + m.


- The first line of the proof moves the universally quantified variables n and m into the context. 
- The second moves the hypothesis n = m into the context and gives it the name H. 
- The third tells Coq to rewrite the current goal (n + n = m + m) by replacing the left side of the equality hypothesis H with the right side.

*(The arrow symbol in the rewrite has nothing to do with implication: it tells Coq to apply the rewrite from left to right. To rewrite from right to left, you can use rewrite <-. Try making this change in the above proof and see what difference it makes.)*

## Proof by Case Analysis

 In general, unknown, hypothetical values (arbitrary numbers, booleans, lists, etc.) can block simplification.

    Theorem plus_1_neq_0_firsttry : ∀ n : nat,
      beq_nat (n + 1) 0 = false.
    Proof.
      intros n.
      simpl. (* does nothing! *)
    Abort.


- The definitions of both beq_nat and + begin by performing a match on their first argument.
- But here, the first argument to + is the unknown number n and the argument to beq_nat is the compound expression n + 1; neither can be simplified.


- We need to consider the possible forms of n separately.
- The tactic that tells Coq to consider, separately, the cases where n = O and where n = S n' is called destruct.

Fixed:

    Theorem plus_1_neq_0 : ∀ n : nat, beq_nat (n + 1) 0 = false.
    Proof.
      intros n. destruct n as [| n'].
      - reflexivity.
      - reflexivity. Qed.


> The annotation "**as [| n']**" is called an **intro pattern**. It tells Coq what **variable names to introduce in each subgoal**. In general, what goes between the square brackets is a list of lists of names, separated by |. In this case, the first component is empty, since the O constructor is nullary (it doesn't have any arguments). The second component gives a single name, n', since S is a unary constructor.


> The - signs on the second and third lines are called bullets, and they mark the parts of the proof that correspond to each generated subgoal.

The destruct tactic can be used with any inductively defined datatype. For example, we use it next to prove that boolean negation is involutive — i.e., that negation is its own inverse.


    Theorem negb_involutive : ∀ b : bool,
      negb (negb b) = b.
    Proof.
      intros b. destruct b.
      - reflexivity.
      - reflexivity. Qed.

Each pair of calls to reflexivity corresponds to the subgoals that were generated after the execution of the destruct c line right above it.


    Theorem andb_commutative : ∀ b c, andb b c = andb c b.
    Proof.
      intros b c. destruct b.
      - destruct c.
        + reflexivity.
        + reflexivity.
      - destruct c.
        + reflexivity.
        + reflexivity.
    Qed.

Using curly braces:

    Theorem andb3_exchange :
      ∀ b c d, andb (andb b c) d = andb (andb b d) c.
    Proof.
      intros b c d. destruct b.
      - destruct c.
        { destruct d.
          - reflexivity.
          - reflexivity. }
        { destruct d.
          - reflexivity.
          - reflexivity. }
      - destruct c.
        { destruct d.
          - reflexivity.
          - reflexivity. }
        { destruct d.
          - reflexivity.
          - reflexivity. }
    Qed.

Shorthands:

- Mixing intros and destruct:
    Theorem plus_1_neq_0' : ∀ n : nat,
      beq_nat (n + 1) 0 = false.
    Proof.
      intros [|n].
      - reflexivity.
      - reflexivity. Qed.


    Theorem andb_commutative'' :
      ∀ b c, andb b c = andb c b.
    Proof.
      intros [] [].
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
    Qed.

**More on Notation (Optional)**

    Notation "x + y" := (plus x y)
                           (at level 50, left associativity)
                           : nat_scope.
    Notation "x * y" := (mult x y)
                           (at level 40, left associativity)
                           : nat_scope.


> For example, the parameters specified above for + and * say that the expression 1+2*3*4 is shorthand for (1+((2*3)*4)). Coq uses precedence levels from 0 to 100, and left, right, or no associativity.


> Each notation symbol is also associated with a notation scope. Coq tries to guess what scope is meant from context, so when it sees S(O*O) it guesses nat_scope, but when it sees the cartesian product (tuple) type bool*bool(which we'll see in later chapters) it guesses type_scope. 
> Occasionally, it is necessary to help it out with percent-notation by writing (x*y)%nat, and sometimes in what Coq prints it will use %nat to indicate what scope a notation is in.
> Notation scopes also apply to numeral notation (3, 4, 5, etc.), so you may sometimes see 0%nat, which means O (the natural number 0 that we're using in this chapter), or 0%Z, which means the Integer zero (which comes from a different part of the standard library).


> Pro tip: Coq's notation mechanism is not especially powerful. Don't expect too much from it!

**Fixpoints and Structural Recursion (Optional)**

    Fixpoint plus' (n : nat) (m : nat) : nat :=
      match n with
      | O ⇒ m
      | S n' ⇒ S (plus' n' m)
      end.


- Coq demands that some argument of *every*Fixpoint definition is "decreasing."
- This requirement is a fundamental feature of Coq's design: In particular, it guarantees that every function that can be defined in Coq will terminate on all inputs. 




----------
## Proof by Induction (Induction)

Before getting started, we need to import all of our definitions from the previous chapter:


    Require Export Basics.

For the Require Export to work, you first need to use coqc to compile Basics.v into Basics.vo.

    coqc Basics.v

The `Print LoadPath.` command may be helpful in sorting out "load path"  issues.

**Proof by Induction**

    Theorem plus_n_O_firsttry : ∀ n:nat,
      n = n + 0.
- 0 is a neutral element for + on the left, using an easy argument based on simplification
- proving the fact that it is also a neutral element on the *right,* can't be done in the same simple way.
-  Just applying reflexivity doesn't work, since the n in n + 0 is an arbitrary unknown number, so the match in the definition of + can't be simplified.
    Theorem plus_n_O_secondtry : ∀ n:nat,
      n = n + 0.
    Proof.
      intros n. destruct n as [| n'].
      - (* n = 0 *)
        reflexivity. (* so far so good... *)
      - (* n = S n' *)
        simpl. (* ...but here we are stuck again *)
    Abort.


- We could use destruct n' to get one step further, but, since n can be arbitrarily large, if we just go on like this we'll never finish.


> The principle of induction over natural numbers: If **P(n)** is some proposition involving a natural number n and we want to show that P holds for all numbers n, we can reason like this:
  - show that **P(O) holds**;
  - show that **for any n', if P(n') holds, then so does P(S n')**;
  - conclude that P(n) holds for all n.

