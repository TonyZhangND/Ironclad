module Common__UpperBound_s {

datatype UpperBound = UpperBoundFinite(n:int) | UpperBoundInfinite()

ghost predicate LeqUpperBound(x:int, u:UpperBound)
{
  match u
    case UpperBoundFinite(n) => x <= n
    case UpperBoundInfinite => true
}

ghost predicate LtUpperBound(x:int, u:UpperBound)
{
  match u
    case UpperBoundFinite(n) => x < n
    case UpperBoundInfinite => true
}
    
ghost function UpperBoundedAddition(x:int, y:int, u:UpperBound):int
{
  if LeqUpperBound(x + y, u) then x + y else u.n
}

}
