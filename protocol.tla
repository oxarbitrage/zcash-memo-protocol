---- MODULE protocol ----
(***************************************************************************)
(* NU7 memo bundles specification                                          *)
(*                                                                         *)
(* This module models a simplified version of the Orchard protocol's memo  *)
(* encryption and decryption process as described in ZIP 231. It includes: *)
(* - A User process that encrypts a memo, constructs a transaction,        *)
(*   and adds it to a transaction pool.                                    *)
(* - A Node process that validates and commits transactions from the pool. *)
(* - A Scanner process that scans the blockchain, decrypts memo data,      *)
(*   and verifies correctness.                                             *)
(* The module uses helper operators which are defined in the Operators     *)
(* module.                                                                 *)
(*                                                                         *)
(* Note: The cryptographic functions (e.g., EncryptionKey, EncryptMemo,    *)
(* DecryptMemo) are abstracted for modeling purposes and do not reflect    *)
(* the full complexity of the real protocol.                               *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, TLC, Sequences, Operators

\* CONSTANTS

\* Full message (as a sequence of characters) that will be encrypted.
memo == << "h", "e", "l", "l", "o", "w", "o", "r", "l", "d" >>
\* Defines the maximum allowed number of memo chunks in a transaction.
memo_chunk_limit == 64
\* The fixed size of each chunk after splitting (and padding, if necessary).
memo_chunk_size == 4

(*--algorithm memo

variables
    \* The transaction pool 
    txPool = {};    
    \* The blockchain
    blockchain = {};
    \* The memo key used for encryption
    memo_key = RandomHash(32);
    \* Randomness salt
    salt = RandomHash(32);
    
\* Encrypt the memo, build a transaction and add it to the pool.
fair process User = "USER"
variables
    encryption_key,
    plaintext_memo_chunks,
    encrypted_memo_chunks,
    tx_builder,
begin
    Encrypt:
        \* Derive the encryption key from the memo key and salt using a (simplified) key derivation function.
        encryption_key := EncryptionKey(memo_key, salt);
        \* Then, split the memo into fixed-size chunks (with padding on the final chunk) using SplitAndPadMemo.
        plaintext_memo_chunks := SplitAndPadMemo(memo, memo_chunk_size);
        \* Finally, encrypt each chunk using the derived encryption key.
        encrypted_memo_chunks := EncryptMemo(encryption_key, plaintext_memo_chunks);
    BuildTx:
        \* Construct the transaction
        tx_builder := 
        [
            f_all_pruned  |-> FALSE, \* set to FALSE, indicating that not all memo chunks are pruned
            salt_or_hash  |-> salt, \* stores the salt used for key derivation
            n_memo_chunks |-> Len(encrypted_memo_chunks), \* the number of memo chunks in the encrypted bundle.
            pruned        |-> <<>>, \* empty since we have a full (non-pruned) memo.
            v_memo_chunks |-> encrypted_memo_chunks, \* the encrypted memo chunks
            actions       |-> {[
                receiver |-> "USER", \* the receiver of the memo
                memo_key |-> memo_key \* the memo key used for encryption
            ]}
        ];
    PushTx:
        await txPool = {};
        txPool := {tx_builder};
end process;

\* Validates and commit transactions
fair process Node = "NODE"
variables 
    tx, 
    valid = TRUE,
    action;
begin
    ValidateTx:
        await txPool /= {};
        tx := CHOOSE transaction \in txPool : TRUE;
        txPool := txPool \ {tx};
        
        action := CHOOSE a \in tx.actions : TRUE;
        
        if Len(tx.v_memo_chunks) > memo_chunk_limit \* Check if the memo bundle is too large
           \/ action.memo_key = <<>> \* Check if the memo key is empty
           \/ ~VerifyTx(tx) then \* Check if the transaction is valid
            valid := FALSE; \* Mark the transaction as invalid
        end if;

        \* Commit valid transactions
        if valid then
            blockchain := blockchain \cup {tx};
        end if;
end process;

\* Scans for transactions belonging to the user and decrypts them
fair process Scanner = "SCANNER"
variables 
    tx,
    decrypted_memo,
    action;
begin
    Scan:
        await Cardinality(blockchain) > 0;
        tx := CHOOSE t \in blockchain : \E a \in t.actions : a.receiver = "USER";
    Decrypt:
        \* Decrypt the memo bundle using the memo key and salt stored in the transaction.
        \* The result should reconstruct the original memo if the encryption was successful.
        decrypted_memo := DecryptedMemoFinal(DecryptMemo(memo_key, tx.salt_or_hash, tx.v_memo_chunks));
        assert memo = decrypted_memo;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ed9dfb75" /\ chksum(tla) = "db0161a6")
\* Process variable tx of process Node at line 79 col 5 changed to tx_
\* Process variable action of process Node at line 81 col 5 changed to action_
CONSTANT defaultInitValue
VARIABLES pc, txPool, blockchain, memo_key, salt, encryption_key, 
          plaintext_memo_chunks, encrypted_memo_chunks, tx_builder, tx_, 
          valid, action_, tx, decrypted_memo, action

vars == << pc, txPool, blockchain, memo_key, salt, encryption_key, 
           plaintext_memo_chunks, encrypted_memo_chunks, tx_builder, tx_, 
           valid, action_, tx, decrypted_memo, action >>

ProcSet == {"USER"} \cup {"NODE"} \cup {"SCANNER"}

Init == (* Global variables *)
        /\ txPool = {}
        /\ blockchain = {}
        /\ memo_key = RandomHash(32)
        /\ salt = RandomHash(32)
        (* Process User *)
        /\ encryption_key = defaultInitValue
        /\ plaintext_memo_chunks = defaultInitValue
        /\ encrypted_memo_chunks = defaultInitValue
        /\ tx_builder = defaultInitValue
        (* Process Node *)
        /\ tx_ = defaultInitValue
        /\ valid = TRUE
        /\ action_ = defaultInitValue
        (* Process Scanner *)
        /\ tx = defaultInitValue
        /\ decrypted_memo = defaultInitValue
        /\ action = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "USER" -> "Encrypt"
                                        [] self = "NODE" -> "ValidateTx"
                                        [] self = "SCANNER" -> "Scan"]

Encrypt == /\ pc["USER"] = "Encrypt"
           /\ encryption_key' = EncryptionKey(memo_key, salt)
           /\ plaintext_memo_chunks' = SplitAndPadMemo(memo, memo_chunk_size)
           /\ encrypted_memo_chunks' = EncryptMemo(encryption_key', plaintext_memo_chunks')
           /\ pc' = [pc EXCEPT !["USER"] = "BuildTx"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, tx_builder, tx_, 
                           valid, action_, tx, decrypted_memo, action >>

BuildTx == /\ pc["USER"] = "BuildTx"
           /\ tx_builder' = [
                                f_all_pruned  |-> FALSE,
                                salt_or_hash  |-> salt,
                                n_memo_chunks |-> Len(encrypted_memo_chunks),
                                pruned        |-> <<>>,
                                v_memo_chunks |-> encrypted_memo_chunks,
                                actions       |-> {[
                                    receiver |-> "USER",
                                    memo_key |-> memo_key
                                ]}
                            ]
           /\ pc' = [pc EXCEPT !["USER"] = "PushTx"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                           plaintext_memo_chunks, encrypted_memo_chunks, tx_, 
                           valid, action_, tx, decrypted_memo, action >>

PushTx == /\ pc["USER"] = "PushTx"
          /\ txPool = {}
          /\ txPool' = {tx_builder}
          /\ pc' = [pc EXCEPT !["USER"] = "Done"]
          /\ UNCHANGED << blockchain, memo_key, salt, encryption_key, 
                          plaintext_memo_chunks, encrypted_memo_chunks, 
                          tx_builder, tx_, valid, action_, tx, decrypted_memo, 
                          action >>

User == Encrypt \/ BuildTx \/ PushTx

ValidateTx == /\ pc["NODE"] = "ValidateTx"
              /\ txPool /= {}
              /\ tx_' = (CHOOSE transaction \in txPool : TRUE)
              /\ txPool' = txPool \ {tx_'}
              /\ action_' = (CHOOSE a \in tx_'.actions : TRUE)
              /\ IF Len(tx_'.v_memo_chunks) > memo_chunk_limit
                    \/ action_'.memo_key = <<>>
                    \/ ~VerifyTx(tx_')
                    THEN /\ valid' = FALSE
                    ELSE /\ TRUE
                         /\ valid' = valid
              /\ IF valid'
                    THEN /\ blockchain' = (blockchain \cup {tx_'})
                    ELSE /\ TRUE
                         /\ UNCHANGED blockchain
              /\ pc' = [pc EXCEPT !["NODE"] = "Done"]
              /\ UNCHANGED << memo_key, salt, encryption_key, 
                              plaintext_memo_chunks, encrypted_memo_chunks, 
                              tx_builder, tx, decrypted_memo, action >>

Node == ValidateTx

Scan == /\ pc["SCANNER"] = "Scan"
        /\ Cardinality(blockchain) > 0
        /\ tx' = (CHOOSE t \in blockchain : \E a \in t.actions : a.receiver = "USER")
        /\ pc' = [pc EXCEPT !["SCANNER"] = "Decrypt"]
        /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                        plaintext_memo_chunks, encrypted_memo_chunks, 
                        tx_builder, tx_, valid, action_, decrypted_memo, 
                        action >>

Decrypt == /\ pc["SCANNER"] = "Decrypt"
           /\ decrypted_memo' = DecryptedMemoFinal(DecryptMemo(memo_key, tx.salt_or_hash, tx.v_memo_chunks))
           /\ Assert(memo = decrypted_memo', 
                     "Failure of assertion at line 116, column 9.")
           /\ pc' = [pc EXCEPT !["SCANNER"] = "Done"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                           plaintext_memo_chunks, encrypted_memo_chunks, 
                           tx_builder, tx_, valid, action_, tx, action >>

Scanner == Scan \/ Decrypt

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == User \/ Node \/ Scanner
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(User)
        /\ WF_vars(Node)
        /\ WF_vars(Scanner)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
