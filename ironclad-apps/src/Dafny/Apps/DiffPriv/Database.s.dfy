include "../../Libraries/Util/be_sequences.s.dfy"
include "Math.s.dfy"

datatype Row = Row_ctor(nonce:seq<int>, data:seq<int>);

static ghost predicate RowValid(row:Row)
{
    IsWordSeq(row.data)
}

static ghost predicate DatabaseValid(db:seq<Row>)
{
    forall i:int :: 0 <= i < |db| ==> RowValid(db[i])
}

static ghost predicate DatabasesIdenticalExceptForOneRow (db1:seq<Row>, db2:seq<Row>, diff_row:int)
{
    |db1| == |db2| &&
    (forall i :: 0 <= i < |db1| && i != diff_row ==> db1[i] == db2[i])
}

static ghost predicate DatabasesSimilar (db1:seq<Row>, db2:seq<Row>)
{
    exists diff_row :: DatabasesIdenticalExceptForOneRow(db1, db2, diff_row)
}

static ghost predicate DatabaseContainsNonce (db:seq<Row>, nonce:seq<int>)
{
    exists i:int :: 0 <= i < |db| && db[i].nonce == nonce
}
