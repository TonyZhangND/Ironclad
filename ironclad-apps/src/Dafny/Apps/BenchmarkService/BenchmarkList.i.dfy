//-
//- List of benchmarks we support.
//-
static function BenchmarkNothing():int { 0 }
static function BenchmarkSha1():int { 1 }
static function BenchmarkSha256():int { 2 }
static function BenchmarkRsaKeyGen():int { 3 }
static function BenchmarkRsaEncrypt():int { 4 }
static function BenchmarkRsaDecrypt():int { 5 }
static function BenchmarkRsaDigestedSign():int { 6 }
static function BenchmarkRsaDigestedVerify():int { 7 }
static function BenchmarkTpmExtractRandom():int { 8 }
static function BenchmarkByteSeqToWordSeq():int { 9 }
static function BenchmarkWordSeqToByteSeq():int { 10 }
static function BenchmarkSha1Raw():int { 11 }
static function BenchmarkSha256Raw():int { 12 }
static function BenchmarkDuplicateArray():int { 13 }
static function BenchmarkFatAdd():int { 14 }
static function BenchmarkFatAddSlowly():int { 15 }
static function BenchmarkMax():int { 16 }
