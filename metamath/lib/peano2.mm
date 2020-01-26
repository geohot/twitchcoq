$(
###############################################################################
            CLASSICAL FIRST-ORDER LOGIC WITH EQUALITY
###############################################################################

  Logic can be defined as the "study of the principles of correct reasoning"
  (Merrilee H. Salmon's 1991 "Informal Reasoning and Informal Logic" in
  _Informal Reasoning and Education_) or as "a formal system using symbolic
  techniques and mathematical methods to establish truth-values" (the Oxford
  English Dictionary).

  This section formally defines the logic system we will use.  In particular,
  it defines symbols for declaring truthful statements, along with rules for
  deriving truthful statements from other truthful statements.  The system
  defined here is classical first-order logic with equality (the most common
  logic system used by mathematicians).

  We begin with a few housekeeping items in pre-logic, and then introduce
  propositional calculus (both its axioms and important theorems that can be
  derived from them).  Propositional calculus deals with general truths about
  well-formed formulas (wffs) regardless of how they are constructed.  This is
  followed by proofs that other axiomatizations of classical propositional
  calculus can be derived from the axioms we have chosen to use.

  We then define predicate calculus, which adds additional symbols and rules
  useful for discussing objects (beyond simply true or false).  In particular,
  it introduces the symbols ` = ` ("equals"), ` e. ` ("is a member of"), and `
  A. ` ("for all").  The first two are called "predicates."  A predicate
  specifies a true or false relationship between its two arguments.

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This section includes a few "housekeeping" mechanisms before we begin
  defining the basics of logic.

$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( Define the syntax and logical typecodes, and declare that our grammar is
     unambiguous (verifiable using the KLR parser, with compositing depth 5).
     (This $ j comment need not be read by verifiers, but is useful for parsers
     like mmj2.) $)
  $( $j
    syntax 'wff';
    syntax '|-' as 'wff';
    unambiguous 'klr 5';
  $)

  $( Declare typographical constant symbols that are not directly used
     in the formalism, but *are* symbols we find useful when
     explaining the formalism. It is much easier to consistently use
     a single typographical system when generating text. $)

  $c & $. $( Ampersand (read: "and-also") $)
  $c => $. $( Big-to (read: "proves") $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Propositional calculus deals with general truths about well-formed formulas
  (wffs) regardless of how they are constructed.  The simplest propositional
  truth is ` ( ph -> ph ) ` , which can be read "if something is true, then it
  is true" - rather trivial and obvious, but nonetheless it must be proved from
  the axioms (see theorem ~ id ).

  Our system of propositional calculus consists of three basic axioms and
  another axiom that defines the modus-ponens inference rule.  It is attributed
  to Jan Lukasiewicz (pronounced woo-kah-SHAY-vitch) and was popularized by
  Alonzo Church, who called it system P2.  (Thanks to Ted Ulrich for this
  information.)  These axioms are ~ ax-1 , ~ ax-2 , ~ ax-3 , and (for modus
  ponens) ~ ax-mp . Some closely followed texts include [Margaris] for the
  axioms and [WhiteheadRussell] for the theorems.

  The propositional calculus used here is the classical system widely used by
  mathematicians.  In particular, this logic system accepts the "law of the
  excluded middle" as proven in ~ exmid , which says that a logical statement
  is either true or not true.  This is an essential distinction of classical
  logic and is not a theorem of intuitionistic logic.

  All 194 axioms, definitions, and theorems for propositional calculus in
  _Principia Mathematica_ (specifically *1.2 through *5.75) are axioms or
  formally proven.  See the Bibliographic Cross-References at
  ~ http://us.metamath.org/mpeuni/mmbiblio.html for a complete
  cross-reference from sources used to its formalization in the Metamath
  Proof Explorer.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ."  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.  So if
     ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( ~ weq and ~ wel ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ."  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  Think of the truth table for an OR gate with input ` ph `
     connected through an inverter.  After we define the axioms of
     propositional calculus ( ~ ax-1 , ~ ax-2 , ~ ax-3 , and ~ ax-mp ), the
     biconditional ( ~ df-bi ), the constant true ` T. ` ( ~ df-tru ), and the
     constant false ` F. ` ( ~ df-fal ), we will be able to prove these truth
     table values: ` ( ( T. -> T. ) <-> T. ) ` ( ~ truimtru ),
     ` ( ( T. -> F. ) <-> F. ) ` ( ~ truimfal ), ` ( ( F. -> T. ) <-> T. ) `
     ( ~ falimtru ), and ` ( ( F. -> F. ) <-> T. ) ` ( ~ falimfal ).  These
     have straightforward meanings, for example, ` ( ( T. -> T. ) <-> T. ) `
     just means "the value of ` ( T. -> T. ) ` is ` T. ` ".

     The left-hand wff is called the antecedent, and the right-hand wff is
     called the consequent.  In the case of ` ( ph -> ( ps -> ch ) ) ` , the
     middle ` ps ` may be informally called either an antecedent or part of the
     consequent depending on context.  Contrast with ` <-> ` ( ~ df-bi ),
     ` /\ ` ( ~ df-an ), and ` \/ ` ( ~ df-or ).

     This is called "material implication" and the arrow is usually read as
     "implies."  However, material implication is not identical to the meaning
     of "implies" in natural language.  For example, the word "implies" may
     suggest a causal relationship in natural language.  Material implication
     does not require any causal relationship.  Also, note that in material
     implication, if the consequent is true then the wff is always true (even
     if the antecedent is false).  Thus, if "implies" means material
     implication, it is true that "if the moon is made of green cheese that
     implies that 5=5" (because 5=5).  Similarly, if the antecedent is false,
     the wff is always true.  Thus, it is true that, "if the moon made of green
     cheese that implies that 5=7" (because the moon is not actually made of
     green cheese).  A contradiction implies anything ( ~ pm2.21i ).  In short,
     material implication has a very specific technical definition, and
     misunderstandings of it are sometimes called "paradoxes of logical
     implication." $)
  wi $a wff ( ph -> ps ) $.

  $( Register '-.' and '->' as primitive expressions (lacking definitions). $)
  $( $j primitive 'wn' 'wi'; $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus (axioms ~ ax-1 through ~ ax-3 and rule ~ ax-mp ) can
  be thought of as asserting formulas that are universally "true" when their
  variables are replaced by any combination of "true" and "false."
  Propositional calculus was first formalized by Frege in 1879, using as his
  axioms (in addition to rule ~ ax-mp ) the wffs ~ ax-1 , ~ ax-2 , ~ pm2.04 ,
  ~ con3 , ~ notnot2 , and ~ notnot1 . Around 1930, Lukasiewicz simplified the
  system by eliminating the third (which follows from the first two, as you can
  see by looking at the proof of ~ pm2.04 ) and replacing the last three with
  our ~ ax-3 . (Thanks to Ted Ulrich for this information.)

  The theorems of propositional calculus are also called _tautologies_.
  Tautologies can be proved very simply using truth tables, based on the
  true/false interpretation of propositional calculus.  To do this, we assign
  all possible combinations of true and false to the wff variables and verify
  that the result (using the rules described in ~ wi and ~ wn ) always
  evaluates to true.  This is called the _semantic_ approach.  Our approach is
  called the _syntactic_ approach, in which everything is derived from axioms.
  A metatheorem called the Completeness Theorem for Propositional Calculus
  shows that the two approaches are equivalent and even provides an algorithm
  for automatically generating syntactic proofs from a truth table.  Those
  proofs, however, tend to be long, since truth tables grow exponentially with
  the number of variables, and the much shorter proofs that we show here were
  found manually.

$)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true."  This rule is sometimes called "detachment," since it detaches
       the minor premise from the major premise.  "Modus ponens" is short for
       "modus ponendo ponens," a Latin phrase that means "the mode that by
       affirming affirms" - remark in [Sanford] p. 39.  This rule is similar to
       the rule of modus tollens ~ mto .

       Note:  In some web page displays such as the Statement List, the
       symbols " ` & ` " and " ` => ` " informally indicate the relationship
       between the hypotheses and the assertion (conclusion), abbreviating the
       English words "and" and "implies."  They are not part of the formal
       language.  (Contributed by NM, 30-Sep-1992.) $)
    ax-mp $a |- ps $.
  $}

  $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  The 3 axioms are also given as Definition 2.1 of
     [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
     simplification" in _Principia Mathematica_ (Theorem *2.02 of
     [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
     assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."  It is
     Proposition 1 of [Frege1879] p. 26, its first axiom.  (Contributed by NM,
     30-Sep-1992.) $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It "distributes" an antecedent over two
     consequents.  This axiom was part of Frege's original system and is known
     as _Frege_ in the literature; see Proposition 2 of [Frege1879] p. 26.  It
     is also proved as Theorem *2.77 of [WhiteheadRussell] p. 108.  The other
     direction of this axiom also turns out to be true, as demonstrated by
     ~ pm5.41 .  (Contributed by NM, 30-Sep-1992.) $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It swaps or "transposes" the order of the
     consequents when negation is removed.  An informal example is that the
     statement "if there are no clouds in the sky, it is not raining" implies
     the statement "if it is raining, there are clouds in the sky."  This axiom
     is called _Transp_ or "the principle of transposition" in _Principia
     Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).  We will also
     use the term "contraposition" for this principle, although the reader is
     advised that in the field of philosophical logic, "contraposition" has a
     different technical meaning.  (Contributed by NM, 30-Sep-1992.) $)
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The definition ~ df-bi in this section is our first definition, which
  introduces and defines the biconditional connective ` <-> ` . We define a wff
  of the form ` ( ph <-> ps ) ` as an abbreviation for
  ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

  Unlike most traditional developments, we have chosen not to have a separate
  symbol such as "Df." to mean "is defined as."  Instead, we will later use the
  biconditional connective for this purpose ( ~ df-or is its first use), as it
  allows us to use logic to manipulate definitions directly.  This greatly
  simplifies many proofs since it eliminates the need for a separate mechanism
  for introducing and eliminating definitions.
$)

  $( Declare the biconditional connective. $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Define the biconditional (logical 'iff').

     The definition ~ df-bi in this section is our first definition, which
     introduces and defines the biconditional connective ` <-> ` .  We define a
     wff of the form ` ( ph <-> ps ) ` as an abbreviation for
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as."  Instead, we will
     later use the biconditional connective for this purpose ( ~ df-or is its
     first use), as it allows us to use logic to manipulate definitions
     directly.  This greatly simplifies many proofs since it eliminates the
     need for a separate mechanism for introducing and eliminating
     definitions.  Of course, we cannot use this mechanism to define the
     biconditional itself, since it hasn't been introduced yet.  Instead, we
     use a more general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` (the definiens i.e. the
     defining expression) in the definition, the definition becomes the
     previously proved theorem ~ bijust .  It is impossible to use ~ df-bi to
     prove any statement expressed in the original language that can't be
     proved from the original axioms, because if we simply replace each
     instance of ~ df-bi in the proof with the corresponding ~ bijust instance,
     we will end up with a proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are not strengthening the language.  To indicate this
     fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just a naming convention for human readability.)

     After we define the constant true ` T. ` ( ~ df-tru ) and the constant
     false ` F. ` ( ~ df-fal ), we will be able to prove these truth table
     values: ` ( ( T. <-> T. ) <-> T. ) ` ( ~ trubitru ),
     ` ( ( T. <-> F. ) <-> F. ) ` ( ~ trubifal ), ` ( ( F. <-> T. ) <-> F. ) `
     ( ~ falbitru ), and ` ( ( F. <-> F. ) <-> T. ) ` ( ~ falbifal ).

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi1 is particularly useful if we want
     to eliminate ` <-> ` from an expression to convert it to primitives.
     Theorem ~ dfbi shows this definition rewritten in an abbreviated form
     after conjunction is introduced, for easier understanding.

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ) .  In some sense ` <-> ` returns true if two
     truth values are equal; ` = ` ( ~ df-cleq ) returns true if two classes
     are equal.  (Contributed by NM, 27-Dec-1992.) $)
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Here we define disjunction (logical 'or') ` \/ ` ( ~ df-or ) and conjunction
  (logical 'and') ` /\ ` ( ~ df-an ). We also define various rules for
  simplifying and applying them, e.g., ~ olc , ~ orc , and ~ orcom .

$)

  $( Declare connectives for disjunction ('or') and conjunction ('and'). $)
  $c \/ $. $( Vee (read:  'or') $)
  $c /\ $. $( Wedge (read:  'and') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.
  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

  $( Define disjunction (logical 'or').  Definition of [Margaris] p. 49.  When
     the left operand, right operand, or both are true, the result is true;
     when both sides are false, the result is false.  For example, it is true
     that ` ( 2 = 3 \/ 4 = 4 ) ` ( ~ ex-or ).  After we define the constant
     true ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we
     will be able to prove these truth table values:
     ` ( ( T. \/ T. ) <-> T. ) ` ( ~ truortru ), ` ( ( T. \/ F. ) <-> T. ) `
     ( ~ truorfal ), ` ( ( F. \/ T. ) <-> T. ) ` ( ~ falortru ), and
     ` ( ( F. \/ F. ) <-> F. ) ` ( ~ falorfal ).

     This is our first use of the biconditional connective in a definition; we
     use the biconditional connective in place of the traditional "<=def=>",
     which means the same thing, except that we can manipulate the
     biconditional connective directly in proofs rather than having to rely on
     an informal definition substitution rule.  Note that if we mechanically
     substitute ` ( -. ph -> ps ) ` for ` ( ph \/ ps ) ` , we end up with an
     instance of previously proved theorem ~ biid .  This is the justification
     for the definition, along with the fact that it introduces a new symbol
     ` \/ ` .  Contrast with ` /\ ` ( ~ df-an ), ` -> ` ( ~ wi ), ` -/\ `
     ( ~ df-nan ), and ` \/_ ` ( ~ df-xor ) .  (Contributed by NM,
     27-Dec-1992.) $)
  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

  $( Define conjunction (logical 'and').  Definition of [Margaris] p. 49.  When
     both the left and right operand are true, the result is true; when either
     is false, the result is false.  For example, it is true that
     ` ( 2 = 2 /\ 3 = 3 ) ` .  After we define the constant true ` T. `
     ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be able
     to prove these truth table values: ` ( ( T. /\ T. ) <-> T. ) `
     ( ~ truantru ), ` ( ( T. /\ F. ) <-> F. ) ` ( ~ truanfal ),
     ` ( ( F. /\ T. ) <-> F. ) ` ( ~ falantru ), and
     ` ( ( F. /\ F. ) <-> F. ) ` ( ~ falanfal ).

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ) .  (Contributed by NM, 5-Jan-1993.) $)
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff definition to include 3-way disjunction ('or'). $)
  w3o $a wff ( ph \/ ps \/ ch ) $.
  $( Extend wff definition to include 3-way conjunction ('and'). $)
  w3a $a wff ( ph /\ ps /\ ch ) $.

  $( These abbreviations help eliminate parentheses to aid readability. $)

  $( Define disjunction ('or') of three wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of three wff's.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for alternative denial ('nand'). $)
  $c -/\ $. $( Overlined 'wedge' (read:  'nand') $)

  $( Extend wff definition to include alternative denial ('nand'). $)
  wnan $a wff ( ph -/\ ps ) $.

  $( Define incompatibility, or alternative denial ('not-and' or 'nand').  This
     is also called the Sheffer stroke, represented by a vertical bar, but we
     use a different symbol to avoid ambiguity with other uses of the vertical
     bar.  In the second edition of Principia Mathematica (1927), Russell and
     Whitehead used the Sheffer stroke and suggested it as a replacement for
     the "or" and "not" operations of the first edition.  However, in practice,
     "or" and "not" are more widely used.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. -/\ T. ) <-> F. ) `
     ( ~ trunantru ), ` ( ( T. -/\ F. ) <-> T. ) ` ( ~ trunanfal ),
     ` ( ( F. -/\ T. ) <-> T. ) ` ( ~ falnantru ), and
     ` ( ( F. -/\ F. ) <-> T. ) ` ( ~ falnanfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` \/_ `
     ( ~ df-xor ) .  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  df-nan $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'xor'
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for exclusive disjunction ('xor'). $)
  $c \/_ $. $( Underlined 'vee' (read:  'xor') $)

  $( Extend wff definition to include exclusive disjunction ('xor'). $)
  wxo $a wff ( ph \/_ ps ) $.

  $( Define exclusive disjunction (logical 'xor').  Return true if either the
     left or right, but not both, are true.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. \/_ T. ) <-> F. ) `
     ( ~ truxortru ), ` ( ( T. \/_ F. ) <-> T. ) ` ( ~ truxorfal ),
     ` ( ( F. \/_ T. ) <-> T. ) ` ( ~ falxortru ), and
     ` ( ( F. \/_ F. ) <-> F. ) ` ( ~ falxorfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` -/\ `
     ( ~ df-nan ) .  (Contributed by FL, 22-Nov-2010.) $)
  df-xor $a |- ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
       Universal quantifier for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it isn't ordinarily part of propositional calculus, the universal
  quantifier ` A. ` is introduced here so that the soundness of definition
  ~ df-tru can be checked by the same algorithm that is used for predicate
  calculus.  Its first real use is in definition ~ df-ex in the predicate
  calculus section below.  For those who want propositional calculus to be
  self-contained i.e. to use wff variables only, the alternate definition
  ~ dftru2 may be adopted and this subsection moved down to the start of the
  subsection with ~ wex below.  However, the use of ~ dftru2 as a definition
  requires a more elaborate definition checking algorithm that we prefer to
  avoid.

$)

  $( Declare new symbols needed for predicate calculus. $)
  $c A. $. $( "inverted A" universal quantifier (read:  "for all") $)
  $c setvar $. $( Individual variable type (read:  "the following is an
             individual (set) variable" $)

  $( Add 'setvar' as a typecode for bound variables. $)
  $( $j syntax 'setvar'; bound 'setvar'; $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.wal $f setvar x $.
    $( Extend wff definition to include the universal quantifier ('for all').
       ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ."  Typically,
       in its final application ` ph ` would be replaced with a wff containing
       a (free) occurrence of the variable ` x ` , for example ` x = y ` .  In
       a universe with a finite number of objects, "for all" is equivalent to a
       big conjunction (AND) with one wff for each possible case of ` x ` .
       When the universe is infinite (as with set theory), such a
       propositional-calculus equivalent is not possible because an infinitely
       long formula has no meaning, but conceptually the idea is the same. $)
    wal $a wff A. x ph $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Equality predicate for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it isn't ordinarily part of propositional calculus, the equality
  predicate ` = ` is introduced here so that the soundness of definition
  ~ df-tru can be checked by the same algorithm as is used for predicate
  calculus.  Its first real use is in theorem ~ equs3 in the predicate calculus
  section below.  For those who want propositional calculus to be
  self-contained i.e. to use wff variables only, the alternate definition
  ~ dftru2 may be adopted and this subsection moved down to just above ~ weq
  below.  However, the use of ~ dftru2 as a definition requires a more
  elaborate definition checking algorithm that we prefer to avoid.
$)

  $c class $.

  $( Add 'class' as a typecode. $)
  $( $j syntax 'class'; $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.cv $f setvar x $.
    $( This syntax construction states that a variable ` x ` , which has been
       declared to be a setvar variable by $f statement vx, is also a class
       expression.  This can be justified informally as follows.  We know that
       the class builder ` { y | y e. x } ` is a class by ~ cab .  Since (when
       ` y ` is distinct from ` x ` ) we have ` x = { y | y e. x } ` by
       ~ cvjust , we can argue that the syntax " ` class x ` " can be viewed as
       an abbreviation for " ` class { y | y e. x } ` ".  See the discussion
       under the definition of class in [Jech] p. 4 showing that "Every set can
       be considered to be a class."

       While it is tempting and perhaps occasionally useful to view ~ cv as a
       "type conversion" from a setvar variable to a class variable, keep in
       mind that ~ cv is intrinsically no different from any other
       class-building syntax such as ~ cab , ~ cun , or ~ c0 .

       For a general discussion of the theory of classes and the role of ~ cv ,
       see ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The description above applies to set theory, not predicate calculus.
       The purpose of introducing ` class x ` here, and not in set theory where
       it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus from the ~ wceq of set theory, so that we don't
       overload the ` = ` connective with two syntax definitions.  This is done
       to prevent ambiguity that would complicate some Metamath parsers.) $)
    cv $a class x $.
  $}

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  ${
    $v A $.
    $v B $.
    $( Temporary declarations of ` A ` and ` B ` . $)
    cA.wceq $f class A $.
    cB.wceq $f class B $.
    $( Extend wff definition to include class equality.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no
       difference.  The class variables ` A ` and ` B ` are introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.  See ~ df-cleq for more information on the set
       theory usage of ~ wceq .) $)
    wceq $a wff A = B $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                Define the true and false constants
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c T. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  ${
    $v x $.
    $v y $.
    $( Temporary declarations of ` x ` and ` y ` for local use by ~ df-tru .
       These will be redeclared globally in the predicate calculus section. $)
    vx.tru $f setvar x $.
    vy.tru $f setvar y $.
    $( Soundness justification theorem for ~ df-tru .  (Contributed by Mario
       Carneiro, 17-Nov-2013.)  (Revised by NM, 11-Jul-2019.) $)
    trujust $p |- ( ( A. x x = x -> A. x x = x )
              <-> ( A. y y = y -> A. y y = y ) ) $=
      ( cv wceq wal wi id 2th ) ACZIDAEZJFBCZKDBEZLFJGLGH $.

    $( Definition of the truth value "true", or "verum", denoted by ` T. ` .
       This is a tautology, as proved by ~ tru .  In this definition, an
       instance of ~ id is used as the definiens, although any tautology, such
       as an axiom, can be used in its place.  This particular ~ id instance
       was chosen so this definition can be checked by the same algorithm that
       is used for predicate calculus.  This definition should be referenced
       directly only by ~ tru , and other proofs should depend on ~ tru
       (directly or indirectly) instead of this definition, since there are
       many alternative ways to define ` T. ` .  (Contributed by Anthony Hart,
       13-Oct-2010.)  (Revised by NM, 11-Jul-2019.)
       (New usage is discouraged.) $)
    df-tru $a |- ( T. <-> ( A. x x = x -> A. x x = x ) ) $.

    $( The truth value ` T. ` is provable.  (Contributed by Anthony Hart,
       13-Oct-2010.) $)
    tru $p |- T. $=
      ( vx.tru wtru cv wceq wal wi id df-tru mpbir ) BACZJDAEZKFKGAHI $.
  $}

  $c F. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Definition of the truth value "false", or "falsum", denoted by ` F. ` .
     See also ~ df-tru .  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  df-fal $a |- ( F. <-> -. T. ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Half adder and full adder in propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus deals with truth values, which can be interpreted as
  bits. Using this, we can define the half adder and full adder in pure
  propositional calculus, and show their basic properties.

  Here is a short description. We code the bit 0 by ` F. ` and 1 by ` T. ` .
  Even though ` hadd ` and ` cadd ` are invariant under permutation of their
  arguments, assume for the sake of concreteness that ` ph ` (resp. ` ps ` ) is
  the i^th bit of the first (resp. second) number to add (with the convention
  that the i^th bit is the multiple of 2^i in the base-2 representation), and
  that ` ch ` is the i^th carry (with the convention that the 0^th carry is 0).
  Then, ` hadd ( ph , ps , ch ) ` gives the i^th bit of the sum, and
  ` cadd ( ph , ps , ch ) ` gives the (i+1)^th carry.
  Then, addition is performed by iteration from i = 0 to
  i = 1 + (max of the number of digits of the two summands) by "updating" the
  carry.
$)

  $c hadd cadd $.
  $c , $.  $( Comma (also used for unordered pair notation later) $)

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  whad $a wff hadd ( ph , ps , ch ) $.

  $( Define the half adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  wcad $a wff cadd ( ph , ps , ch ) $.

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  df-had $a |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $.

  $( Define the half adder carry, which is true when at least two arguments are
     true.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  df-cad $a |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
    Predicate calculus with equality:  Tarski's system S2 (1 rule, 6 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Here we extend the language of wffs with predicate calculus, which allows us
  to talk about individual objects in a domain of discussion (which for us will
  be the universe of all sets, so we call them "setvar variables") and make
  true/false statements about predicates, which are relationships between
  objects, such as whether or not two objects are equal.  In addition, we
  introduce universal quantification ("for all", e.g. ~ ax-4 ) in order to
  make statements about whether a wff holds for every object in the domain of
  discussion.  Later we introduce existential quantification ("there exists",
  ~ df-ex ) which is defined in terms of universal quantification.

  Our axioms are really axiom _schemes_, and our wff and setvar variables are
  metavariables ranging over expressions in an underlying "object language."
  This is explained here:  ~ mmset.html#axiomnote .

  Our axiom system starts with the predicate calculus axiom schemes system S2
  of Tarski defined in his 1965 paper, "A Simplified Formalization of Predicate
  Logic with Identity" [Tarski].  System S2 is defined in the last paragraph on
  p. 77, and repeated on p. 81 of [KalishMontague].  We do not include scheme
  B5 (our ~ sp ) of system S2 since [KalishMontague] shows it to be logically
  redundant (Lemma 9, p. 87, which we prove as theorem ~ spw below).

  Theorem ~ spw can be used to prove any _instance_ of ~ sp having mutually
  distinct setvar variables and no wff metavariables.  However, it seems that
  ~ sp in its general form cannot be derived from only Tarski's schemes.  We do
  not include B5 i.e. ~ sp as part of what we call "Tarski's system" because we
  want it to be the smallest set of axioms that is logically complete with
  no redundancies.  We later prove ~ sp as theorem ~ axc5 using the auxiliary
  axioms that make our system metalogically complete.

  Our version of Tarski's system S2 consists of propositional calculus
  ( ~ ax-mp , ~ ax-1 , ~ ax-2 , ~ ax-3 ) plus ~ ax-gen , ~ ax-4 , ~ ax-5 ,
  ~ ax-6 , ~ ax-7 , ~ ax-8 , and ~ ax-9 . The last 3 are equality axioms that
  represent 3 sub-schemes of Tarski's scheme B8.  Due to its side-condition
  ("where ` ph ` is an atomic formula and ` ps ` is obtained by replacing an
  occurrence of the variable ` x ` by the variable ` y ` "), we cannot
  represent his B8 directly without greatly complicating our scheme language,
  but the simpler schemes ~ ax-7 , ~ ax-8 , and ~ ax-9 are sufficient for set
  theory and much easier to work with.

  Tarski's system is exactly equivalent to the traditional axiom system in most
  logic textbooks but has the advantage of being easy to manipulate with a
  computer program, and its simpler metalogic (with no built-in notions of
  "free variable" and "proper substitution") is arguably easier for a
  non-logician human to follow step by step in a proof (where "follow" means
  being able to identify the substitutions that were made, without necessarily
  a higher-level understanding).  In particular, it is logically complete in
  that it can derive all possible object-language theorems of predicate
  calculus with equality, i.e. the same theorems as the traditional system can
  derive.

  However, for efficiency (and indeed a key feature that makes Metamath
  successful), our system is designed to derive reusable theorem schemes
  (rather than object-language theorems) from other schemes.  From this
  "metalogical" point of view, Tarski's S2 is not complete.  For example, we
  cannot derive scheme ~ sp , even though (using ~ spw ) we can derive all
  instances of it that don't involve wff metavariables or bundled set
  metavariables.  (Two set metavariables are "bundled" if they can be
  substituted with the same set metavariable i.e. do not have a $d distinct
  variable proviso.)  Later we will introduce auxiliary axiom schemes ~ ax-10 ,
  ~ ax-11 , ~ ax-12 , and ~ ax-13 that are metatheorems of Tarski's system
  (i.e. are logically redundant) but which give our system the property of
  "metalogical completeness," allowing us to prove directly (instead of, say,
  by induction on formula length) all possible schemes that can be expressed in
  our language.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Universal quantifier (continued); define "exists" and "not free"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The universal quantifier was introduced above in ~ wal for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with the
  first "real" use of it.
$)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $v t $.
  $( Let ` x ` be an individual variable. $)
  vx $f setvar x $.
  $( Let ` y ` be an individual variable. $)
  vy $f setvar y $.
  $( Let ` z ` be an individual variable. $)
  vz $f setvar z $.
  $( Let ` w ` be an individual variable. $)
  vw $f setvar w $.
  $( Let ` v ` be an individual variable. $)
  vv $f setvar v $.
  $( Let ` u ` be an individual variable. $)
  vu $f setvar u $.
  $( Let ` t ` be an individual variable. $)
  vt $f setvar t $.

  $( Register 'A.' as a primitive expression (lacking a definition). $)
  $( $j primitive 'wal'; $)

  $( Declare the existential quantifier symbol. $)
  $c E. $.   $( Backwards E (read:  "there exists") $)

  $( Extend wff definition to include the existential quantifier ("there
     exists"). $)
  wex $a wff E. x ph $.

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true."  Definition of [Margaris]
     p. 49.  (Contributed by NM, 10-Jan-1993.) $)
  df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

  $( Theorem 19.7 of [Margaris] p. 89.  (Contributed by NM, 12-Mar-1993.) $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wex wn wal df-ex con2bii ) ABCADBEABFG $.

  $c F/ $.  $( The not-free symbol. $)

  $( Extend wff definition to include the not-free predicate. $)
  wnf $a wff F/ x ph $.

  $( Define the not-free predicate for wffs.  This is read " ` x ` is not free
     in ` ph ` ".  Not-free means that the value of ` x ` cannot affect the
     value of ` ph ` , e.g., any occurrence of ` x ` in ` ph ` is effectively
     bound by a "for all" or something that expands to one (such as "there
     exists").  In particular, substitution for a variable not free in a wff
     does not affect its value ( ~ sbf ).  An example of where this is used is
     ~ stdpc5 .  See ~ nf2 for an alternative definition which does not involve
     nested quantifiers on the same variable.

     Not-free is a commonly used constraint, so it is useful to have a notation
     for it.  Surprisingly, there is no common formal notation for it, so here
     we devise one.  Our definition lets us work with the not-free notion
     within the logic itself rather than as a metalogical side condition.

     To be precise, our definition really means "effectively not free," because
     it is slightly less restrictive than the usual textbook definition for
     not-free (which only considers syntactic freedom).  For example, ` x ` is
     effectively not free in the bare expression ` x = x ` (see ~ nfequid ),
     even though ` x ` would be considered free in the usual textbook
     definition, because the value of ` x ` in the expression ` x = x ` cannot
     affect the truth of the expression (and thus substitution will not change
     the result).

     This predicate only applies to wffs.  See ~ df-nfc for a not-free
     predicate for class variables.  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  df-nf $a |- ( F/ x ph <-> A. x ( ph -> A. x ph ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Rule scheme ax-gen (Generalization)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ allt shows the
       special case ` A. x T. ` .  Theorem ~ spi shows we can go the other way
       also: in other words we can add or remove universal quantifiers from the
       beginning of any theorem as required.  (Contributed by NM,
       3-Jan-1993.) $)
    ax-gen $a |- A. x ph $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         Axiom scheme ax-4 (Quantified Implication)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105 and Theorem
     19.20 of [Margaris] p. 90.  It is restated as ~ alim for labelling
     consistency.  It should be used only by ~ alim .  (Contributed by NM,
     21-May-2008.)  (New usage is discouraged.) $)
  ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-5 (Distinctness) - first use of $d
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom of Distinctness.  This axiom quantifies a variable over a formula
       in which it does not occur.  Axiom C5 in [Megill] p. 444 (p. 11 of the
       preprint).  Also appears as Axiom B6 (p. 75) of system S2 of [Tarski]
       p. 77 and Axiom C5-1 of [Monk2] p. 113.

       (See comments in ~ ax5ALT about the logical redundancy of ~ ax-5 in the
       presence of our obsolete axioms.)

       This axiom essentially says that if ` x ` does not occur in ` ph ` ,
       i.e. ` ph ` does not depend on ` x ` in any way, then we can add the
       quantifier ` A. x ` to ` ph ` with no further assumptions.  By ~ sp , we
       can also remove the quantifier (unconditionally).  (Contributed by NM,
       10-Jan-1993.) $)
    ax-5 $a |- ( ph -> A. x ph ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Define proper substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ $. $( Left bracket $)
  $c / $. $( Slash. $)
  $c ] $.  $( Right bracket $)

  $( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").
     (Contributed by NM, 24-Jan-2006.) $)
  wsb $a wff [ y / x ] ph $.

  $( Indicate that the variable "y" is free in wsb even though it could
     potentially bind occurrences in "ph". $)
  $( $j free_var 'wsb' with 'y'; $)

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean "the wff
     that results from the proper substitution of ` y ` for ` x ` in the wff
     ` ph ` ."  That is, ` y ` properly replaces ` x ` .  For example,
     ` [ x / y ] z e. y ` is the same as ` z e. x ` , as shown in ~ elsb4 .  We
     can also use ` [ y / x ] ph ` in place of the "free for" side condition
     used in traditional predicate calculus; see, for example, ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, " ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` ."  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another version that mixes free and bound variables is
     ~ dfsb3 .  When ` x ` and ` y ` are distinct, we can express proper
     substitution with the simpler expressions of ~ sb5 and ~ sb6 .

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` .  (Contributed by NM, 10-May-1993.) $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Axiom scheme ax-6 (Existence)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  This axiom tells us is that at least
     one thing exists.  In this form (not requiring that ` x ` and ` y ` be
     distinct) it was used in an axiom system of Tarski (see Axiom B7' in
     footnote 1 of [KalishMontague] p. 81.)  It is equivalent to axiom scheme
     C10' in [Megill] p. 448 (p. 16 of the preprint); the equivalence is
     established by ~ axc10 and ~ ax6fromc10 .  A more convenient form of this
     axiom is ~ ax6e , which has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ http://us.metamath.org/award2003.html .

     ~ ax-6 can be proved from the weaker version ~ ax6v requiring that the
     variables be distinct; see theorem ~ ax6 .

     ~ ax-6 can also be proved from the Axiom of Separation (in the form that
     we use that axiom, where free variables are not universally quantified).
     See theorem ~ ax6vsep .

     Except by ~ ax6v , this axiom should not be referenced directly.  Instead,
     use theorem ~ ax6 .  (Contributed by NM, 10-Jan-1993.)
     (New usage is discouraged.) $)
  ax-6 $a |- -. A. x -. x = y $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Axiom scheme ax-7 (Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  This axiom scheme
     is a sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom C7 of [Monk2] p. 105 and Axiom Scheme C8' in [Megill] p. 448 (p. 16
     of the preprint).

     The equality symbol was invented in 1527 by Robert Recorde.  He chose a
     pair of parallel lines of the same length because "noe .2. thynges, can be
     moare equalle."

     Note that this axiom is still valid even when any two or all three of
     ` x ` , ` y ` , and ` z ` are replaced with the same variable since they
     do not have any distinct variable (Metamath's $d) restrictions.  Because
     of this, we say that these three variables are "bundled" (a term coined by
     Raph Levien).  (Contributed by NM, 10-Jan-1993.) $)
  ax-7 $a |- ( x = y -> ( x = z -> y = z ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom scheme ax-8 (Left Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Left Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the left-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C12' in [Megill] p. 448 (p. 16 of the preprint).
     "Non-logical" means that the predicate is not a primitive of predicate
     calculus proper but instead is an extension to it.  "Binary" means that
     the predicate has two arguments.  In a system of predicate calculus with
     equality, like ours, equality is not usually considered to be a
     non-logical predicate.  In systems of predicate calculus without equality,
     it typically would be.  (Contributed by NM, 30-Jun-1993.) $)
  ax-8 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom scheme ax-9 (Right Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Right Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the right-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C13' in [Megill] p. 448 (p. 16 of the preprint).
     (Contributed by NM, 21-Jun-1993.) $)
  ax-9 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Logical redundancy of ax-10 , ax-11 , ax-12 , ax-13
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The original axiom schemes of Tarski's predicate calculus are ~ ax-4 ,
  ~ ax-5 , ~ ax6v , ~ ax-7 , ~ ax-8 , and ~ ax-9 , together with rule
  ~ ax-gen .  See ~ http://us.metamath.org/mpeuni/mmset.html#compare .  They
  are given as axiom schemes B4 through B8 in [KalishMontague] p. 81.  These
  are shown to be logically complete by Theorem 1 of [KalishMontague] p. 85.

  The axiom system of set.mm includes the auxiliary axiom schemes ~ ax-10 ,
  ~ ax-11 , ~ ax-12 , and ~ ax-13 , which are not part of Tarski's axiom
  schemes.  Each object language instance of them is provable from Tarski's
  axioms, so they are logically redundant.  However, they are conjectured not
  to be provable directly _as schemes_ from Tarski's axiom schemes using only
  Metamath's direct substitution rule.  They are used to make our system
  "metalogically complete" i.e. able to prove directly all possible schemes
  with wff and set metavariables, bundled or not, whose object-language
  instances are valid.  ( ~ ax-12 has been proved to be required; see
  ~ http://us.metamath.org/award2003.html#9a .  Metalogical independence of the
  other three are open problems.)

  (There are additional predicate calculus axiom schemes included in set.mm
  such as ~ ax-c5 , but they can all be proved as theorems from the above.)

  Terminology:  Two set (individual) metavariables are "bundled" in an axiom or
  theorem scheme when there is no distinct variable constraint ($d) imposed on
  them.  (The term "bundled" is due to Raph Levien.)  For example, the ` x `
  and ` y ` in ~ ax-6 are bundled, but they are not in ~ ax6v . We also say
  that a scheme is bundled when it has at least one pair of bundled set
  metavariables.  If distinct variable conditions are added to all set
  metavariable pairs in a bundled scheme, we call that the "principal" instance
  of the bundled scheme.  For example, ~ ax6v is the principal instance of
  ~ ax-6 . Whenever a common variable is substituted for two or more bundled
  variables in an axiom or theorem scheme, we call the substitution instance
  "degenerate".  For example, the instance ` -. A. x -. x = x ` of ~ ax-6 is
  degenerate.  An advantage of bundling is ease of use since there are fewer
  distinct variable restrictions ($d) to be concerned with.  There is also a
  small economy in being able to state principal and degenerate instances
  simultaneously.  A disadvantage is that bundling may present difficulties in
  translations to other proof languages, which typically lack the concept (in
  part because their variables often represent the variables of the object
  language rather than metavariables ranging over them).

  Because Tarski's axiom schemes are logically complete, they can be used to
  prove any object-language instance of ~ ax-10 , ~ ax-11 , ~ ax-12 , and
  ~ ax-13 . "Translating" this to Metamath, it means that Tarski's axioms can
  prove any substitution instance of ~ ax-10 , ~ ax-11 , ~ ax-12 , or ~ ax-13
  in which (1) there are no wff metavariables and (2) all set metavariables are
  mutually distinct i.e. are not bundled.  In effect this is mimicking the
  object language by pretending that each set metavariable is an
  object-language variable.  (There may also be specific instances with wff
  metavariables and/or bundling that are directly provable from Tarski's axiom
  schemes, but it isn't guaranteed.  Whether all of them are possible is part
  of the still open metalogical independence problem for our additional axiom
  schemes.)

  It can be useful to see how this can be done, both to show that our
  additional schemes are valid metatheorems of Tarski's system and to be able
  to translate object language instances of our proofs into proofs that would
  work with a system using only Tarski's original schemes.  In addition, it may
  (or may not) provide insight into the conjectured metalogical independence of
  our additional schemes.

  The theorem schemes ~ ax10w , ~ ax11w , ~ ax12w , and ~ ax13w are derived
  using only Tarski's axiom schemes, showing that Tarski's schemes can be used
  to derive all substitution instances of ~ ax-10 , ~ ax-11 , ~ ax-12 , and
  ~ ax-13 meeting conditions (1) and (2).  (The "w" suffix stands for "weak
  version".)  Each hypothesis of ~ ax10w , ~ ax11w , and ~ ax12w is of the form
  ` ( x = y -> ( ph <-> ps ) ) ` where ` ps ` is an auxiliary or "dummy" wff
  metavariable in which ` x ` doesn't occur.  We can show by induction on
  formula length that the hypotheses can be eliminated in all cases meeting
  conditions (1) and (2).  The example ~ ax12wdemo illustrates the techniques
  (equality theorems and bound variable renaming) used to achieve this.

  We also show the degenerate instances for axioms with bundled variables in
  ~ ax11dgen , ~ ax12dgen , ~ ax13dgen1 , ~ ax13dgen2 , ~ ax13dgen3 , and
  ~ ax13dgen4 . (Their proofs are trivial, but we include them to be thorough.)
  Combining the principal and degenerate cases _outside_ of Metamath, we show
  that the bundled schemes ~ ax-10 , ~ ax-11 , ~ ax-12 , and ~ ax-13 are
  schemes of Tarski's system, meaning that all object language instances they
  generate are theorems of Tarski's system.

  It is interesting that Tarski used the bundled scheme ~ ax-6 in an older
  system, so it seems the main purpose of his later ~ ax6v was just to show
  that the weaker unbundled form is sufficient rather than an aesthetic
  objection to bundled free and bound variables.  Since we adopt the
  bundled ~ ax-6 as our official axiom, we  show that the degenerate
  instance holds in ~ ax6dgen .

  The case of ~ sp is curious:  originally an axiom of Tarski's system, it was
  proved logically redundant by Lemma 9 of [KalishMontague] p. 86.  However,
  the proof is by induction on formula length, and the scheme form
  ` A. x ph -> ph ` apparently cannot be proved directly from Tarski's other
  axiom schemes.  The best we can do seems to be ~ spw , again requiring
  substitution instances of ` ph ` that meet conditions (1) and (2) above.
  Note that our direct proof ~ sp requires ~ ax-12 , which is not part of
  Tarski's system.

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
   Predicate calculus with equality:  Auxiliary axiom schemes (4 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  In this section we introduce four additional schemes ~ ax-10 , ~ ax-11 ,
  ~ ax-12 , and ~ ax-13 that are not part of Tarski's system but can be proved
  (outside of Metamath) as theorem schemes of Tarski's system.  These are
  needed to give our system the property of "metalogical completeness," which
  means that we can prove (with Metamath) all possible theorem schemes
  expressible in our language of wff metavariables ranging over object-language
  wffs and set metavariables ranging over object-language individual variables.

  To show that these schemes are valid metatheorems of Tarski's system S2,
  above we proved from Tarski's system theorems ~ ax10w , ~ ax11w , ~ ax12w ,
  and ~ ax13w , which show that any object-language instance of these schemes
  (emulated by having no wff metavariables and requiring all set
  metavariables to be mutually distinct) can be proved using only the schemes
  in Tarski's system S2.

  An open problem is to show that these four additional schemes are mutually
  _metalogically_ independent and metalogically independent from Tarski's.  So
  far, independence of ~ ax-12 from all others has been shown, and
  independence of Tarski's ~ ax-6 from all others has been shown; see
  items 9a and 11 on ~ http://us.metamath.org/award2003.html .

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Axiom scheme ax-10 (Quantified Negation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax10w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  It means that ` x ` is not
     free in ` -. A. x ph ` (Contributed by NM, 21-May-2008.)  Use its alias
     ~ hbn1 instead.  (New usage is discouraged.) $)
  ax-10 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Axiom scheme ax-11 (Quantifier Commutation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  Axiom scheme C6' in [Megill] p. 448 (p. 16 of the
     preprint).  Also appears as Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of
     [Monk2] p. 113.  This axiom scheme is logically redundant (see ~ ax11w )
     but is used as an auxiliary axiom to achieve metalogical completeness.
     (Contributed by NM, 12-Mar-1993.) $)
  ax-11 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Axiom scheme ax-12 (Substitution)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-c15 and was replaced with this
     shorter ~ ax-12 in Jan. 2007.  The old axiom is proved from this one as
     theorem ~ axc15 .  Conversely, this axiom is proved from ~ ax-c15 as
     theorem ~ ax12 .

     Juha Arpiainen proved the metalogical independence of this axiom (in the
     form of the older axiom ~ ax-c15 ) from the others on 19-Jan-2006.  See
     item 9a at ~ http://us.metamath.org/award2003.html .

     See ~ ax12v and ~ ax12v2 for other equivalents of this axiom that (unlike
     this axiom) have distinct variable restrictions.

     This axiom scheme is logically redundant (see ~ ax12w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     22-Jan-2007.) $)
  ax-12 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Axiom scheme ax-13 (Quantified Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Equality.  One of the equality and substitution axioms
     of predicate calculus with equality.

     An equivalent way to express this axiom that may be easier to understand
     is ` ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ` (see
     ~ ax13b ).  Recall that in the intended interpretation, our variables are
     metavariables ranging over the variables of predicate calculus (the object
     language).  In order for the first antecedent ` -. x = y ` to hold, ` x `
     and ` y ` must have different values and thus cannot be the same
     object-language variable (so they are effectively "distinct variables"
     even though no $d is present).  Similarly, ` x ` and ` z ` cannot be the
     same object-language variable.  Therefore, ` x ` will not occur in the wff
     ` y = z ` when the first two antecedents hold, so analogous to ~ ax-5 ,
     the conclusion ` ( y = z -> A. x y = z ) ` follows.  Note that ~ ax-5
     cannot prove this directly because it requires $d statements.

     The original version of this axiom was ~ ax-c9 and was replaced with this
     shorter ~ ax-13 in December 2015.  The old axiom is proved from this one
     as theorem ~ axc9 .  Conversely, this axiom is proved from ~ ax-c9 as
     theorem ~ ax13 .

     The primary purpose of this axiom is to provide a way to introduce the
     quantifier ` A. x ` on ` y = z ` even when ` x ` and ` y ` are substituted
     with the same variable.  In this case, the first antecedent becomes
     ` -. x = x ` and the axiom still holds.

     Although this version is shorter, the original version ~ axc9 may be more
     practical to work with because of the "distinctor" form of its
     antecedents.  A typical application of ~ axc9 is in ~ dvelimh which
     converts a distinct variable pair to the distinctor antecedent
     ` -. A. x x = y ` .  In particular, it is conjectured that it is not
     possible to prove ~ ax6 from ~ ax6v without this axiom.

     This axiom can be weakened if desired by adding distinct variable
     restrictions on pairs ` x , z ` and ` y , z ` .  To show that, we add
     these restrictions to theorem ~ ax13v and use only ~ ax13v for further
     derivations.  Thus, ~ ax13v should be the only theorem referencing this
     axiom.  Other theorems can reference either ~ ax13v (preferred) or
     ~ ax13 .

     This axiom scheme is logically redundant (see ~ ax13w ) but is used as an
     auxiliary axiom to achieve metalogical completeness (i.e. so that all
     possible cases of bundling can be proved; see text linked at
     ~ mmtheorems.html#wal ).  It is not known whether this axiom can be
     derived from the others.  (Contributed by NM, 21-Dec-2015.)
     (New usage is discouraged.) $)
  ax-13 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
               Existential uniqueness
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare new symbols needed for uniqueness notation. $)
  $c E! $.  $( Backwards E exclamation point. $)
  $c E* $.  $( Backwards E superscript *. $)

  $( Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)
  weu $a wff E! x ph $.

  $( Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)
  wmo $a wff E* x ph $.

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (Contributed by NM,
       11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wb wal wex equequ2 bibi2d albidv cbvexv bitri ) ABCFZGZBHZCIABEF
      ZGZBHZEIABDFZGZBHZDIQTCECEFZPSBUDORACEBJKLMTUCEDEDFZSUBBUERUAAEDBJKLMN $.

    $( Alternate proof of ~ eujust illustrating the use of ~ dvelim .
       (Contributed by NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wal wb wex equequ2 bibi2d albidv sps wn hbnae ax-5 notbid dvelim
      wi df-ex drex1 alrimih naecoms a1i cbv2h syl 3bitr4g pm2.61i ) CDFZCGZABC
      FZHZBGZCIZABDFZHZBGZDIZHUMUQCDUIUMUQHCUIULUPBUIUKUOACDBJKLZMUAUJNZUMNZCGZ
      NUQNZDGZNUNURUTVBVDUTUTDGZCGVBVDHUTVECCDCOCDDOUBUTVAVCCDVAVADGSDCABEFZHZB
      GZNZVADCEVIDPECFZVHUMVJVGULBVJVFUKAECBJKLQRUCVIVCCDEVICPEDFZVHUQVKVGUPBVK
      VFUOAEDBJKLQRUIVAVCHSUTUIUMUQUSQUDUEUFQUMCTUQDTUGUH $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3v , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.) $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 .  (Contributed by NM, 8-Mar-1995.) $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.