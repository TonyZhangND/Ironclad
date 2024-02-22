include "../Math/power2.s.dfy"
include "bytes_and_words.s.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- Sequence types
//-////////////////////////////////////////////////////////////////////////////

static ghost predicate IsDigitSeq(place_value:int, digits:seq<int>)
{
    forall i {:trigger digits[i]} :: 0<=i<|digits| ==> 0 <= digits[i] < place_value
}

static ghost predicate IsBitSeq(bs:seq<int>)
{
    IsDigitSeq(power2(1), bs)
}

static ghost predicate IsByteSeq(os:seq<int>)
{
    IsDigitSeq(power2(8), os)
}

static ghost predicate IsWordSeq(ws:seq<int>)
{
    IsDigitSeq(power2(32), ws)
}

static ghost predicate IsBitSeqOfLen(os:seq<int>, len:int)
{
    IsBitSeq(os) && |os| == len
}

static ghost predicate IsByteSeqOfLen(os:seq<int>, len:int)
{
    IsByteSeq(os) && |os| == len
}

static ghost predicate IsWordSeqOfLen(os:seq<int>, len:int)
{
    IsWordSeq(os) && |os| == len
}

//-////////////////////////////////////////////////////////////////////////////
//- Relationships among sequences of different digit sizes
//- (bit, byte, word, and ghost int)
//-////////////////////////////////////////////////////////////////////////////

//- BE/LE refers to the endianness of the transformation. There's no
//- inherent endianness in a sequence until it's interpreted.


static ghost function {:opaque} BEDigitSeqToInt_private(place_value:int, digits:seq<int>) : int
    decreases |digits|;
{
    if (digits==[]) then
        0
    else
        
        
        BEDigitSeqToInt_private(place_value, digits[0..|digits|-1])*place_value + digits[|digits|-1]
}

static ghost function BEDigitSeqToInt(place_value:int, digits:seq<int>) : int
    requires IsDigitSeq(place_value, digits);
{
    BEDigitSeqToInt_private(place_value, digits)
}

static ghost function {:autoReq}BEBitSeqToInt(bits:seq<int>) : int
{
    BEDigitSeqToInt(power2(1), bits)
}

static ghost function {:autoReq} BEByteSeqToInt(bytes:seq<int>) : int
{
    BEDigitSeqToInt(power2(8), bytes)
}

static ghost function {:autoReq} BEWordSeqToInt(words:seq<int>) : int
{
    BEDigitSeqToInt(power2(32), words)
}




static ghost function {:opaque} BEIntToDigitSeq_private(place_value:int, min_places:int, v:int) : seq<int>
    decreases if v>min_places then v else min_places;
{
    if (1<place_value && (0<v || 0<min_places)) then
        (/*call_lemma:*/ property_dafny_cant_see_about_div(v, place_value);
        BEIntToDigitSeq_private(place_value, min_places-1, v/place_value)
            + [ v % place_value ])
    else
        []
}








static lemma {:axiom} property_dafny_cant_see_about_div(n:int, d:int)
    requires 1<d;
    ensures 0<n ==> n/d < n;
    ensures n<=0 ==> n/d <= 0;

static ghost function BEIntToDigitSeq(place_value:int, min_places:int, v:int) : seq<int>
{
        BEIntToDigitSeq_private(place_value, min_places, v)
}

//-////////////////////////////////////////////////////////////////////////////

static ghost predicate BEDigitSeqEqInt(place_value:int, digits:seq<int>, v:int)
{
    IsDigitSeq(place_value, digits)
    && BEDigitSeqToInt(place_value, digits)==v
}

static ghost predicate BEBitSeqEqInt(bitseq:seq<int>, v:int)
{
    BEDigitSeqEqInt(2, bitseq, v)
}

static ghost predicate BEBitSeqEqByte(bitseq:seq<int>, byte:int)
{
    IsByte(byte) && BEBitSeqEqInt(bitseq, byte)
}

static ghost predicate BEBitSeqEqWord(bitseq:seq<int>, word:int)
{
    IsWord(word) && BEBitSeqEqInt(bitseq, word)
}

static ghost predicate BEByteSeqEqInt(byteseq:seq<int>, v:int)
{
    BEDigitSeqEqInt(256, byteseq, v)
}

static ghost predicate BEByteSeqEqWord(byteseq:seq<int>, word:int)
{
    IsWord(word) && BEByteSeqEqInt(byteseq, word)
}

static ghost predicate BEWordSeqEqInt(byteseq:seq<int>, v:int)
{
    BEDigitSeqEqInt(power2(32), byteseq, v)
}

static ghost predicate BEBitSeqEqByteSeq(bitseq:seq<int>, byteseq:seq<int>)
{
    exists v:int ::
        BEBitSeqEqInt(bitseq, v) && BEByteSeqEqInt(byteseq, v)
}

static ghost predicate BEBitSeqEqWordSeq(bitseq:seq<int>, wordseq:seq<int>)
{
    exists v:int ::
        BEBitSeqEqInt(bitseq, v) && BEWordSeqEqInt(wordseq, v)
}

static ghost predicate BEByteSeqEqWordSeq(byteseq:seq<int>, wordseq:seq<int>)
{
    exists v:int ::
        BEByteSeqEqInt(byteseq, v) && BEWordSeqEqInt(wordseq, v)
}

//-////////////////////////////////////////////////////////////////////////////
//- Generator ghost functions (as opposed to recognizer ghost predicates)
//-////////////////////////////////////////////////////////////////////////////





//

static ghost function BEIntToByteSeq(x: int) : seq<int>
{
    BEIntToDigitSeq(power2(8), 0, x)
}

static ghost function BEWordToFourBytes(x: int) : seq<int>
    requires Word32(x);
{
    BEIntToDigitSeq(power2(8), 4, x)
}

static ghost function BEWordToBitSeq(x:int) : seq<int>
{
    BEIntToDigitSeq(power2(1), 32, x)
}

static ghost function {:autoReq} BEWordSeqToBitSeq(wordseq:seq<int>) : seq<int>
{
   BEIntToDigitSeq(power2(1), |wordseq|*32, BEDigitSeqToInt(power2(32), wordseq))
}

static ghost function {:autoReq} BEByteSeqToBitSeq(byteseq:seq<int>) : seq<int>
{
    BEIntToDigitSeq(power2(1), |byteseq|*8, BEDigitSeqToInt(power2(8), byteseq))
}

static ghost function {:autoReq} BEWordSeqToByteSeq(wordseq:seq<int>) : seq<int>
{
    BEIntToDigitSeq(power2(8), |wordseq|*4, BEDigitSeqToInt(power2(32), wordseq))
}

static ghost function RepeatDigit(digit:int, count:int) : seq<int>
    decreases count;
{
    if (count<=0) then [] else RepeatDigit(digit, count-1) + [digit]
}

static ghost function {:opaque} Reverse(os:seq<int>) : seq<int>
    decreases |os|;
{
    if (os==[]) then
        []
    else
        [os[|os|-1]] + Reverse(os[0..|os|-1])
}
