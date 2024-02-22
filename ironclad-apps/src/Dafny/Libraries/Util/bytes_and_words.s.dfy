include "../Math/power2.s.dfy"

static ghost predicate IsBit(b:int)
{
    0 <= b < 2
}

static ghost predicate IsByte(b:int)
{
    0 <= b < 256
}

//


//
static ghost predicate Word16(x:int)
{
    0 <= x < 0x10000
}

static ghost predicate Word32(x: int)
{
    0 <= x < power2(32)
}

//

//

static ghost predicate IsWord(w: int)
{
    Word32(w)
}
