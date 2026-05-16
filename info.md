## Inline

Определения `(.), id, beta, eta`


05.03
Checked GHC.Core looks scary

13.03
Try to parse like -ddump-parsed-ast
Don't know hoe to analyze it

14.03
Check papers. Found one which use similar steps, could be useful 
* [articale-1](https://dl.acm.org/doi/epdf/10.1145/3299711.3242756)
* [artical-2](https://dl.acm.org/doi/epdf/10.1145/2804302.2804303)

D. Ros´en. Proving equational Haskell properties using automated
theorem provers. Master’s thesis, University of Gothenburg, 2012.


09.04
Try make it as a plugin



TODO
Find each expression from the file 
For each expression identify first-applied-action
Do i want to make as plugin?


16.04
Leave Core for now. makes beta reductions for us
Stage Rewrite because it useful and still readable. Or typechecked will go?
For collecting info Not everywhere, we need a little bit of context for eq. res
Some mix of manual walk and uniplate on latter stages

16.04
Make fund and find diff

17.04 
What about subst? look into Core and rewrite to it

20.04
Implemented using core
Add subctExpr
Now write manual B-reduction because why not


Subst only onec
B-reduction
Subst like func L func R and beta


If it's function
Find where it applied as: f [args]
Subst all ocurence? or /Simplify separate f
get f' [args]. Construct back
back let

for now belive that if it's function applying it allways App (App ...)


22.04
Протестировать свойства классических монад
introduce postulates:
    Postulate as a class
    postulate as a function. Find all usages in file
    Postulate as ANN {-# ANN myFunc "my-tag" #-} annotation
Доказали -> запостулировали
Или разрешения порядка и циклов

Add List comments
DEl control_expr. We can find regex easier


add let-eqivalence without subst it inside? make my own alpha-eq


03.05
Names resolution. especialy when subst postulates
Check how subst resolves it, what names postulates had 
get postulates 

04.05
Postulates subst is just reach rewriting rules
Make it as Simplifier. Don't forget flag

Rewrite it all as a monad with: IO, Context, Exception
Deciding the order of monads and which exectly

06.05
PROBLEMS TO SOLVE
    Rules (postulates) subst all occurances
    Bad alphaEq
    Don't deal with where
    No builtIn functions

add several steps at onece

accurate alphaEq!!!!!!!!!!!!!!!!

07.05
WHAT HAPPEND IN REWRITING RULES
and why i have suffered almost a day on it

Okay the problem was, that when you rewrite rule, you provide [free variables]
including id for first_applied_function_lhs (FAFL) (main for subst rule)
For succesfully rewrite rule this id should contain idInfo about coressponding rule.

it doesn't matter what rule_fn is. it just schold correspond with idInfo which 
simplifier will get from inScope or some-where-else 
(i don't know how it done for Prelude. 

* I thought error was that id in InScope was old (without some idInfo) and not as in declaration
* The real problem was that this idInfo doesn't contain RULE

* it is not. So DEFINE EVERYTHING myself
* they are were some things which allowd rewrite rules for >>=
    * it is classOp and it first of tryRules)

it means
* Add rule to idInfo
* add everything (from expr and rhs to inScope)

When you run it by simplifying whole program it contains them automatically

rewriting rules is just subst of FAFL. I separate them from subst function because 
rewriting rules should have all of the parameters but function can stay lambda
And one of my goals is to check user!!!!


-2) several comment on one subst 
-1) order
+0) ask about вложенных rules. 
    * lookupRules
    * simplifyRUles lhs == simplifyRUles rhs 
+1) where
    RESULT. 
    If function never used by itself it deleted in Core
    Force user to write separate defs or preserve them from desugar
    UPD. I could deal with functions and force preserve them (moinline)
    but i can't do the same with dead code -- lemmas. so no where for them
+2) alphaEq

09.05
Done 
    ordered  -- need to fix error. I want to analyze everything else i guess
    alphaEq

Next: lookupRules is better i guess...
why lookup/no lookup
lookup do something with extra args



case ... of and fold don't match because of that i guess
--  Actualy, the problem with diff is only
-- func arg1 arg2 ... = func arg1' arg2' ...
-- Because if it is anything like
-- func arg1 arg2 ... = g_func ...
-- diff will see it

- One of the solutions is to mark this kind of functions beforhand. (f_b, f_body), f_b == f_bodyB <- collectFunc
- Diff is the first matching the comment if it is function application (I don't like it!!! the whole reason to write evaluation manualy is to be able to simplify them not as compiler)
- Diff in Arg, okay try analyze. Error? okay, make step back try to analyze App 

WE have problem in diff only when it is recursion with the same function name


-- fix many files correct search of functions
-- add instances 


Особенности постулатов с inst. Нельязя Monad => в правой части если нет в левой