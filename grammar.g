value : inductive
     | assertion

// ident
first_letter : ("a".."z") | ("A".."Z") | "_"
subsequent_letter : ("a".."z") | ("A".."Z") | ("0".."9") | "'" | "_"
ident : first_letter subsequent_letter*
name : ident | "_"

// term
term : "forall" binders "," term

// binder (is wrong)
binder : name
       | name [":" term]
binders : binder+

inductive : "Inductive"

assertion : assertion_keyword ident [binders] ":" term "."
assertion_keyword : "Theorem" | "Lemma"


