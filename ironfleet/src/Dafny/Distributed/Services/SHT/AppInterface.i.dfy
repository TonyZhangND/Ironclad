include "AppInterface.s.dfy"
include "Bytes.s.dfy"

module AppInterface_i refines AppInterface_s {
import opened Bytes_s
export Spec
    provides Native__NativeTypes_s
    reveals Key // provides Key REVIEW: triggers a Dafny bug
    provides Value
    provides KeyLt
    provides lemma_KeyOrdering
    provides KeyMin, ValidKey, ValidValue, MarshallSHTKey, MarshallSHTValue
export All reveals *

type Key(==, !new) = uint64
type Value = seq<byte>

predicate KeyLt(ka:Key, kb:Key) 
{
    ka < kb 
}

lemma lemma_KeyOrdering()
{
}

ghost function max_key_len() : int { 16 }  
ghost function max_val_len() : int { 1024 }  

ghost predicate ValidKey(key:Key)
{
    true 
}

ghost predicate ValidValue(v:Value)
{
    |v| < max_val_len()
}

function KeyMin() : Key { 0 }

ghost function MarshallSHTKey(k:Key) : seq<byte>
{
    Uint64ToBytes(k)
}

ghost function MarshallSHTValue(v:Value) : seq<byte>
{
    if |v| < 0x1_0000_0000_0000_0000 then
        Uint64ToBytes(|v| as uint64) + v
    else
        []  // We only handle reasonably sized values
}
}
