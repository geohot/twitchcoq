grammar start;

start : outermost_scope_stmt* ;
outermost_scope_stmt : constant_stmt | stmt ;
constant_stmt : '$c' constant+ '$.' ;

stmt : block | variable_stmt | disjoint_stmt | hypothesis_stmt | assert_stmt ;
block : '${' stmt* '$}' ;

variable_stmt : '$v' variable+ '$.' ;
disjoint_stmt : '$d' variable variable variable* '$.' ;
hypothesis_stmt : floating_stmt | essential_stmt ;

floating_stmt : LABEL '$f' typecode variable '$.' ;
essential_stmt : LABEL '$e' typecode MATH_SYMBOL* '$.' ;

assert_stmt : axiom_stmt | provable_stmt ;

axiom_stmt : LABEL '$a' typecode MATH_SYMBOL* '$.' ;
provable_stmt : LABEL '$p' typecode MATH_SYMBOL* '$=' proof '$.' ;

proof : uncompressed_proof | compressed_proof ;
uncompressed_proof : (LABEL | '?')+ ;
compressed_proof : '(' LABEL* ')' COMPRESSED_PROOF_BLOCK+ ;

typecode : constant ;

constant : MATH_SYMBOL ;
variable : MATH_SYMBOL ;

LCHAR : ('a'..'z') | ('A'..'Z') | ('0'..'9') | '.' | '-' | '_' ;
CHAR : ('a'..'z') | ('A'..'Z') | ('0'..'9') | '\'' | '_' | '|' | '-' | '+' | '*' | '=' | '<' | '>' | '(' | ')' | '.' | ':' | ',' | '\\' | '[' | ']' | '/' | '~' | '!' | '?' | '@' | '&' | '{' | '}' | '^' | '`' | '"' | ';' | '#' ;

MATH_SYMBOL : CHAR+ ;
LABEL : LCHAR+ ;
COMPRESSED_PROOF_BLOCK : (('A'..'Z') | '?')+ ;
COMMENT : '$(' /(.)+?/ '$)' ;

/*
%ignore ' '
%ignore '\n'
%ignore '\t'
%ignore '\r'
%ignore COMMENT
*/

