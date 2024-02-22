static ghost predicate is_prefix(prefix:seq<int>, super:seq<int>)
{
    |super| >= |prefix|
    && super[..|prefix|] == prefix
}

static ghost predicate is_suffix(suffix:seq<int>, super:seq<int>)
{
    |super| >= |suffix|
    && super[|suffix|..] == suffix
}
