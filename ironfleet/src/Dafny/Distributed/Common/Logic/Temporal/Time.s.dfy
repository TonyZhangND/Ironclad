include "Temporal.s.dfy"

module Temporal__Time_s {
import opened Temporal__Temporal_s
import opened Collections__Maps2_s

ghost function{:opaque} eventuallywithin(x:temporal, span:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i {:trigger sat(i, eventuallywithin(x, span, timefun))} ::
               sat(i, eventuallywithin(x, span, timefun)) <==>
               sat(i, eventual(beforeabsolutetime(x, timefun[i] + span, timefun)))
{
  stepmap(imap j :: sat(j, eventual(beforeabsolutetime(x, timefun[j] + span, timefun))))
}

ghost function{:opaque} alwayswithin(x:temporal, span:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i {:trigger sat(i, alwayswithin(x, span, timefun))} ::
               sat(i, alwayswithin(x, span, timefun)) <==>
               sat(i, always(untilabsolutetime(x, timefun[i] + span, timefun)))
{
  stepmap(imap j :: sat(j, always(untilabsolutetime(x, timefun[j] + span, timefun))))
}

ghost function{:opaque} before(t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i {:trigger sat(i, before(t, timefun))} ::
             sat(i, before(t, timefun)) <==> timefun[i] <= t
{
  stepmap(imap i :: timefun[i] <= t)
}

ghost function{:opaque} after(t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i{:trigger sat(i, after(t, timefun))} ::
             sat(i, after(t, timefun)) <==> (timefun[i] >= t)
{
  stepmap(imap i :: timefun[i] >= t)
}

ghost function nextbefore(action:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  and(action, next(before(t, timefun)))
}

ghost function nextafter(action:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
{
  and(action, next(after(t, timefun)))
}

ghost function{:opaque} eventuallynextwithin(action:temporal, span:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i {:trigger sat(i, eventuallynextwithin(action, span, timefun))} ::
             sat(i, eventuallynextwithin(action, span, timefun)) <==>
             sat(i, eventual(nextbefore(action, timefun[i] + span, timefun)))
{
  stepmap(imap i :: sat(i, eventual(nextbefore(action, timefun[i] + span, timefun))))
}

ghost function{:opaque} beforeabsolutetime(x:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i {:trigger sat(i, beforeabsolutetime(x, t, timefun))} ::
             sat(i, beforeabsolutetime(x, t, timefun)) <==>
             sat(i, x) && timefun[i] <= t
{
  and(x, before(t, timefun))
}

ghost function{:opaque} untilabsolutetime(x:temporal, t:int, timefun:imap<int, int>):temporal
  requires imaptotal(timefun)
  ensures  forall i {:trigger sat(i, untilabsolutetime(x, t, timefun))} ::
             sat(i, untilabsolutetime(x, t, timefun)) <==>
             timefun[i] <= t ==> sat(i, x)
{
  imply(before(t, timefun), x)
}

ghost function actionsWithin(i1:int, i2:int, x:temporal):set<int>
{
  set i | i1 <= i < i2 && sat(i, x)
}

ghost function countWithin(i1:int, i2:int, x:temporal):int
{
  |actionsWithin(i1, i2, x)|
}

} 
