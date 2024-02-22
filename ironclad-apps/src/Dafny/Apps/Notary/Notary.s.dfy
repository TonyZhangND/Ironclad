include "../../Libraries/Util/be_sequences.s.dfy"
include "../../Libraries/Crypto/RSA/RSASpec.s.dfy"
include "../../Libraries/Crypto/RSA/rfc4251.s.dfy"
include "../Common/CommonState.s.dfy"
include "../../Drivers/TPM/tpm-device.s.dfy"

//-///////////////////////////////////////////////////
//- Structures
//-///////////////////////////////////////////////////

datatype NotaryState = NotaryStateConstructor(counter:nat);

//-///////////////////////////////////////////////////
//- Helpers
//-///////////////////////////////////////////////////

static ghost function {:autoReq} NotaryCounterAdvanceStatement(new_counter_value:nat, message:seq<int>) : seq<int>
{
    [34] + rfc4251_mpint_encoding(new_counter_value) + message
}

//-///////////////////////////////////////////////////
//- Specifications for correct method operation
//-///////////////////////////////////////////////////

//- This ghost function is used to ensure that notary initialization operates correctly.

static ghost predicate {:autoReq} NotaryInitializeValid(notary_state:NotaryState)
{
    notary_state.counter == 0
}

//- This ghost function is used to ensure that NotaryAdvanceCounter operates
//- correctly.  That method is supposed to advance the given counter to the
//- next counter value.  It should then return an attestation that the
//- counter was advanced.

static ghost predicate {:autoReq} NotaryAdvanceCounterValid(in_state:NotaryState, out_state:NotaryState, common_state:CommonState,
                                                      message_in:seq<int>, notary_statement_out:seq<int>, notary_attestation_out:seq<int>)
{
    out_state.counter == in_state.counter + 1 &&
    WellformedRSAKeyPairSpec(common_state.key_pair) &&
    IsByteSeq(message_in) &&
    IsByteSeq(notary_statement_out) &&
    IsByteSeq(notary_attestation_out) &&
    notary_statement_out == NotaryCounterAdvanceStatement(out_state.counter, message_in) &&
    notary_attestation_out == RSASignature(common_state.key_pair, notary_statement_out)
}
