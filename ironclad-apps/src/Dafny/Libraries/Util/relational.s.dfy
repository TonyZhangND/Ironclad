//-//////////////////////////////////////////
//-  Relational interface used by SymDiff
//-//////////////////////////////////////////

//- Dummy ghost functions that are translated into BoogieAsm keywords:
static ghost function left<t>(x:t) : t { x }
static ghost function right<t>(x:t) : t { x }
static ghost predicate relation<t>(x:t) { true }
static ghost predicate public<t>(x:t) { true }

//- Imported ghost functions:
static ghost predicate{:imported} declassified(lg:int, rg:int, l:int, r:int)
