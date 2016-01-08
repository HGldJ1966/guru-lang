Duckki Oe started this page as a reference manual.  Probably we are going to put together a nice PDF reference manual later this fall (2009), but the explanations below might be useful for now.

# Summary of Proof Syntax #

| **join** _term_ _term_ | **join** proves the equality of the two terms by evaluating them. |
|:-----------------------|:------------------------------------------------------------------|
| **clash** _term_ _term_ | **clash** proves the disequality of two terminating terms headed by distinct constructors. |
| **trans** _proof1_ _proof2_ | When _proof1_ proves A = B and _proof2_ proves B = C, then **trans** proves A = C. Or if _proof2_ is a disequality, it proves A != C. |
| **symm** _proof_       | If _proof_ proves A = C, then **symm** proves C = A. This works similarly if _proof_ proves a disequality. |

| **foralli** { _varlist_ }+ **.** _proof_ | _varlist_ is a list of variable declarations in the form (_x1_ : _A1_)...(_xn_ : _An_).  This proves the universal formulas **Forall**(_x1_:_A1_)...(_xn_:_An_). _F_, assuming _proof_ proves _F_ in a context declaring _x1_ to be of classifier _A1_, through _xn_ of classifier _An_. |
|:-----------------------------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **`[`** _proof_ { _argument_ }+ **`]`**  | If _proof_ proves **Forall**(_x1_:_A1_)...(_xn_:_An_)._F_, then this proves the instantiation by the given arguments of that universal formula.                                                                                                                                          |

| **case** _term_ **with** _pattern_ **=>** _proof_ { | _pattern_ **=>** _proof_ }`*` **end** | This does a case split on the value of _term_, which should be a terminating term of inductive type. |
|:--------------------------------------------------------------------------------------------|:-----------------------------------------------------------------------------------------------------|
| **case** _term_ **by** _var1_ _var2_ **with** _pattern_ **=>** _proof_ { | _pattern_ **=>** _proof_ }`*` **end** | _var1_ is instantiated with the proof of the equality of _term_ and each _pattern_. And _var2_ is instantiated with the proof of the equality of **types** of them. |
| **induction** { _param_ }+ **return** _formula_ **with** _pattern_ **=>** _proof_ { | _pattern_ **=>** _proof_ }`*` **end** | **induction** introduces Foralls for each parameter. Even if multiple parameters are given, it does actually induction on the last one. |
| **contra** _proof_ _formula_                                                                | _proof_ should prove a contradiction, and **contra** trivially proves _formula_.                     |

| **existsi** _value_ _formula`*`_ _proof_ | _proof_ should prove _formula`*`_`[`_value_`]` |
|:-----------------------------------------|:-----------------------------------------------|
| **existse** _proof1_ _proof2_            | _proof1_ should prove a formula like `Exists(x:nat).F`, and _proof2_ should prove a formula like `Forall(x:nat)(u:F).F2`. |

| **hypjoin** _term_ _term_ **by** { _proof_ }`*` **end** | This tries to join the two terms, but using also the equations proved by the given proofs.  It is sound and complete: if it says the terms cannot be joined modulo those equations, they truly cannot (without using case-splitting or induction).|
|:--------------------------------------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|



# More Information about the Rules #

## clash ##

| **clash** _term_ _term_ | **clash** proves the disequality of two terminating terms headed by distinct constructors. |
|:------------------------|:-------------------------------------------------------------------------------------------|

**clash** proves the disequality of two different values of the same type, which cannot be proved to be equal. For example, `tt != ff`, `(S Z) != (S (S Z))`. With inductive data types, you cannot construct the same value in multiple ways. That means if two constants are syntactically different, they are unequal by definition.

## contra ##

| **contra** _proof_ _formula_ | the _proof_ should prove a contradiction, and **contra** trivially proves _formula_. |
|:-----------------------------|:-------------------------------------------------------------------------------------|

A contradiction here is an disequality of form `{`t != t `}`. A proof of disequality often involves a **clash** proof.