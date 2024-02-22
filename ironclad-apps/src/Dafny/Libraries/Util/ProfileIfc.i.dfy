static function Tally_TestDigits() : int { 1 }
static function Tally_BigNatSub() : int { 2 }
static function Tally_BigNatModExpCalls() : int { 3 }
static function Tally_BigNatModExpWhileLoops() : int { 4 }
static function Tally_BigNatDivCalls() : int { 5 }
static function Tally_BigNatDivWhileLoops() : int { 6 }

static function Tally_FatNatModExp() : int { 7 }
static function Tally_FatNatMul() : int { 8 }
static function Tally_FatNatMod() : int { 9 }
static function Tally_MillerRabinTest() : int { 10 }

//- Mark these 'ghost' unless profiling to avoid creating runtime code
//- in real build.
static ghost method ResetTally() {}
static ghost method ProfileTally(category:int, value:int) {}
static ghost method DisplayTally() {}

