grammar Math;

start : outermost_scope_stmt* ;
outermost_scope_stmt : constant_stmt | stmt ;
constant_stmt : '$c' constant+ '$.' ;

stmt : block | variable_stmt | disjoint_stmt | hypothesis_stmt | assert_stmt ;
block : '${' stmt* '$}' ;

variable_stmt : '$v' variable+ '$.' ;
disjoint_stmt : '$d' variable variable variable* '$.' ;
hypothesis_stmt : floating_stmt | essential_stmt ;

floating_stmt : LABEL '$f' typecode variable '$.' ;
essential_stmt : LABEL '$e' typecode math_symbol* '$.' ;

assert_stmt : axiom_stmt | provable_stmt ;

axiom_stmt : LABEL '$a' typecode math_symbol* '$.' ;
provable_stmt : LABEL '$p' typecode math_symbol* '$=' proof '$.' ;

proof : uncompressed_proof | compressed_proof ;
uncompressed_proof : math_symbol+ ; // LABEL or ?
compressed_proof : MATHWORD LABEL* MATHWORD math_symbol+ ;
// note, this has to verify by hand, LABEL/MATHWORD are too forgiving

typecode : constant ;

constant : math_symbol ;
variable : math_symbol ;

math_symbol : (LABEL | MATHWORD) ;

fragment LCHAR : ('a'..'z') | ('A'..'Z') | ('0'..'9') | '.' | '-' | '_' ;
fragment CHAR : LCHAR | '\'' | '|' | '+' | '*' | '=' | '<' | '>' | '(' | ')' | ':' | ',' | '\\' | '[' | ']' | '/' | '~' | '!' | '?' | '@' | '&' | '{' | '}' | '^' | '`' | '"' | ';' | '#' ;

LABEL : LCHAR+ ;
MATHWORD : CHAR+ ;

COMMENT : '$(' .*? '$)' -> skip ;
WHITESPACE : (' ' | '\n' | '\t' | '\r')+ -> skip ;


