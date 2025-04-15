---- MODULE protocol ----
(***************************************************************************)
(* NU7 memo bundles specification                                          *)
(*                                                                         *)
(* This specification is a simplified version of the memo bundles protocol *)
(* update to happen at NU7 with the introduction of `V6` transactions.     *)
(*                                                                         *)
(* The protocol is designed to demonstrate the functionality of the        *)
(* encryption and decryption process as described in ZIP-231. It includes: *)
(* - A User process that encrypts a memo, constructs a transaction,        *)
(*   and adds it to a transaction pool.                                    *)
(* - A Node process that validates and commits transactions from the pool. *)
(* To demostrate pruning, all chunks are eventually pruned from the bundle.*)
(* - A Scanner process that scans the blockchain, decrypts memo data,      *)
(* and verifies correctness.                                               *)
(*                                                                         *)
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
memo_chunk_limit == 2
\* The fixed size of each chunk after splitting (and padding, if necessary).
memo_chunk_size == 6
\* Representation of a pruned chunk.
pruned_chunk == << "p", "r", "u", "n", "e", "d" >>

(*--algorithm memo

variables
    \* Pool where transactions are stored before being validated.
    txPool = {};
    \* The blockchain is a set of transactions.
    blockchain = {};
    \* The memo key used for memo encryption.
    memo_key = RandomHash(32);
    \* Randomness salt used for key derivation.
    salt = RandomHash(32);

    decrypted_memo = <<>>;

define
    \* At least in 1 behaviour, no pruning occurred, decrypted_memo is equal memo.
    DecrypedEqOrig == Cardinality(blockchain) > 0 =>
        <> (decrypted_memo = memo)
    \* At least in 1 behaviour, the first chunk is pruned.
    DecrypedEqPruned1 == Cardinality(blockchain) > 0 =>
        <> (decrypted_memo = pruned_chunk \o SubSeq(memo, memo_chunk_size+1, Len(memo)))
    \* At least in 1 behaviour, the last chunk was pruned.
    DecrypedEqPruned2 == Cardinality(blockchain) > 0 =>
        <> (decrypted_memo = (SubSeq(memo, 1, memo_chunk_size)) \o pruned_chunk)
    \* At least in 1 behaviour, all chunks were pruned.
    DecrypedEqAllPruned == Cardinality(blockchain) > 0 =>
        <> (decrypted_memo = (pruned_chunk \o pruned_chunk))
end define;
    
\* Encrypt the memo, build a transaction and add it to the pool.
fair process User = "USER"
variables
    encryption_key,
    plaintext_memo_chunks,
    encrypted_memo_chunks,
    tx_v6,
begin
    Encrypt:
        \* Derive the encryption key from the memo key and salt using a (simplified) key derivation function.
        encryption_key := EncryptionKey(memo_key, salt);
        \* Split the memo into fixed-size chunks (with padding on the final chunk).
        plaintext_memo_chunks := SplitAndPadMemo(memo, memo_chunk_size);
        \* Encrypt each chunk using the derived encryption key.
        encrypted_memo_chunks := EncryptMemo(encryption_key, plaintext_memo_chunks);
    BuildTx:
        \* Construct the transaction
        tx_v6 :=
        [
            f_all_pruned  |-> FALSE, \* No memo chunk is pruned at memo creation.
            salt_or_hash  |-> salt, \* stores the salt used for key derivation
            n_memo_chunks |-> Len(encrypted_memo_chunks), \* the number of memo chunks in the encrypted bundle.
            pruned        |-> [ _i \in 1..Len(encrypted_memo_chunks) |-> 0 ], \* a sequence of 0's indicating no chunk is pruned.
            v_memo_chunks |-> encrypted_memo_chunks, \* the encrypted memo chunks
            actions       |-> {[
                receiver |-> "USER", \* the receiver of the memo
                memo_key |-> memo_key, \* the memo key used for encryption
                amount   |-> 0 \* the amount of the transaction
            ]}
        ];
    PushTx:
        await txPool = {};
        txPool := {tx_v6};
end process;

\* Validates, prunes, and commits transactions
fair process Node = "NODE"
variables 
    tx, 
    new_tx,
    i = 1;
begin
    ValidateTx:
        await txPool /= {};
        tx := CHOOSE transaction \in txPool : TRUE;
        txPool := txPool \ {tx};

        assert Len(tx.v_memo_chunks) <= memo_chunk_limit;
        assert (CHOOSE a \in tx.actions : TRUE).memo_key # <<>>;
        assert VerifyTx(tx);

        \* Commit valid transactions
        blockchain := blockchain \cup {tx};
    PruneChunks:
        \* Loop over each memo chunk in the transaction until all are pruned.
        \* This will produce a state for each chunk that is pruned.
        while i <= Len(tx.v_memo_chunks) do
            if tx.v_memo_chunks[i].chunk /= pruned_chunk then
                new_tx := 
                [ tx EXCEPT
                    !.v_memo_chunks[i].chunk = pruned_chunk, \* H(AEAD(MemoChunk, memo_key))
                    !.pruned[i] = 1 ];
            end if;
            i := i + 1;
            \* Update the blockchain: replace the original transaction with the updated one.
            blockchain := (blockchain \ {tx}) \cup {new_tx};
            \* Update the transaction variable to point to the new transaction.
            tx := new_tx;
        end while;
    UpdateTx:
        \* When all chunks have been processed, update overall transaction fields:
        new_tx := 
            [ tx EXCEPT 
                !.f_all_pruned = TRUE,
                !.salt_or_hash = RandomHash(32) \* `memo_bundle_digest = H(concat(memo_chunk_digests))`
            ];
        \* Update the blockchain: replace the original transaction with the updated one.
        blockchain := (blockchain \ {tx}) \cup {new_tx};
        tx := new_tx;
end process;

\* Scans for transactions belonging to the user and decrypts them
fair process Scanner = "SCANNER"
variables 
    tx;
begin
    Scan:
        await Cardinality(blockchain) > 0;
        tx := CHOOSE t \in blockchain : \E a \in t.actions : a.receiver = "USER";
    Decrypt:
        \* Decrypt the memo bundle using the memo key and salt stored in the transaction.
        decrypted_memo := DecryptedMemoFinal(DecryptMemo(memo_key, tx.salt_or_hash, tx.v_memo_chunks));
        \* If all chunks were pruned in transaction, then decrypted_memo should be all pruned, 
        \* and the `salt_or_hash` field should be a memo_bundle_digest.
        if tx.f_all_pruned = TRUE then
            assert decrypted_memo = (pruned_chunk \o pruned_chunk);
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9e513778" /\ chksum(tla) = "810c1a86")
\* Process variable tx of process Node at line 104 col 5 changed to tx_
CONSTANT defaultInitValue
VARIABLES pc, txPool, blockchain, memo_key, salt, decrypted_memo

(* define statement *)
DecrypedEqOrig == Cardinality(blockchain) > 0 =>
    <> (decrypted_memo = memo)

DecrypedEqPruned1 == Cardinality(blockchain) > 0 =>
    <> (decrypted_memo = pruned_chunk \o SubSeq(memo, memo_chunk_size+1, Len(memo)))

DecrypedEqPruned2 == Cardinality(blockchain) > 0 =>
    <> (decrypted_memo = (SubSeq(memo, 1, memo_chunk_size)) \o pruned_chunk)

DecrypedEqAllPruned == Cardinality(blockchain) > 0 =>
    <> (decrypted_memo = (pruned_chunk \o pruned_chunk))

VARIABLES encryption_key, plaintext_memo_chunks, encrypted_memo_chunks, tx_v6, 
          tx_, new_tx, i, tx

vars == << pc, txPool, blockchain, memo_key, salt, decrypted_memo, 
           encryption_key, plaintext_memo_chunks, encrypted_memo_chunks, 
           tx_v6, tx_, new_tx, i, tx >>

ProcSet == {"USER"} \cup {"NODE"} \cup {"SCANNER"}

Init == (* Global variables *)
        /\ txPool = {}
        /\ blockchain = {}
        /\ memo_key = RandomHash(32)
        /\ salt = RandomHash(32)
        /\ decrypted_memo = <<>>
        (* Process User *)
        /\ encryption_key = defaultInitValue
        /\ plaintext_memo_chunks = defaultInitValue
        /\ encrypted_memo_chunks = defaultInitValue
        /\ tx_v6 = defaultInitValue
        (* Process Node *)
        /\ tx_ = defaultInitValue
        /\ new_tx = defaultInitValue
        /\ i = 1
        (* Process Scanner *)
        /\ tx = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "USER" -> "Encrypt"
                                        [] self = "NODE" -> "ValidateTx"
                                        [] self = "SCANNER" -> "Scan"]

Encrypt == /\ pc["USER"] = "Encrypt"
           /\ encryption_key' = EncryptionKey(memo_key, salt)
           /\ plaintext_memo_chunks' = SplitAndPadMemo(memo, memo_chunk_size)
           /\ encrypted_memo_chunks' = EncryptMemo(encryption_key', plaintext_memo_chunks')
           /\ pc' = [pc EXCEPT !["USER"] = "BuildTx"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, decrypted_memo, 
                           tx_v6, tx_, new_tx, i, tx >>

BuildTx == /\ pc["USER"] = "BuildTx"
           /\ tx_v6' = [
                           f_all_pruned  |-> FALSE,
                           salt_or_hash  |-> salt,
                           n_memo_chunks |-> Len(encrypted_memo_chunks),
                           pruned        |-> [ _i \in 1..Len(encrypted_memo_chunks) |-> 0 ],
                           v_memo_chunks |-> encrypted_memo_chunks,
                           actions       |-> {[
                               receiver |-> "USER",
                               memo_key |-> memo_key,
                               amount   |-> 0
                           ]}
                       ]
           /\ pc' = [pc EXCEPT !["USER"] = "PushTx"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, decrypted_memo, 
                           encryption_key, plaintext_memo_chunks, 
                           encrypted_memo_chunks, tx_, new_tx, i, tx >>

PushTx == /\ pc["USER"] = "PushTx"
          /\ txPool = {}
          /\ txPool' = {tx_v6}
          /\ pc' = [pc EXCEPT !["USER"] = "Done"]
          /\ UNCHANGED << blockchain, memo_key, salt, decrypted_memo, 
                          encryption_key, plaintext_memo_chunks, 
                          encrypted_memo_chunks, tx_v6, tx_, new_tx, i, tx >>

User == Encrypt \/ BuildTx \/ PushTx

ValidateTx == /\ pc["NODE"] = "ValidateTx"
              /\ txPool /= {}
              /\ tx_' = (CHOOSE transaction \in txPool : TRUE)
              /\ txPool' = txPool \ {tx_'}
              /\ Assert(Len(tx_'.v_memo_chunks) <= memo_chunk_limit, 
                        "Failure of assertion at line 113, column 9.")
              /\ Assert((CHOOSE a \in tx_'.actions : TRUE).memo_key # <<>>, 
                        "Failure of assertion at line 114, column 9.")
              /\ Assert(VerifyTx(tx_'), 
                        "Failure of assertion at line 115, column 9.")
              /\ blockchain' = (blockchain \cup {tx_'})
              /\ pc' = [pc EXCEPT !["NODE"] = "PruneChunks"]
              /\ UNCHANGED << memo_key, salt, decrypted_memo, encryption_key, 
                              plaintext_memo_chunks, encrypted_memo_chunks, 
                              tx_v6, new_tx, i, tx >>

PruneChunks == /\ pc["NODE"] = "PruneChunks"
               /\ IF i <= Len(tx_.v_memo_chunks)
                     THEN /\ IF tx_.v_memo_chunks[i].chunk /= pruned_chunk
                                THEN /\ new_tx' = [ tx_ EXCEPT
                                                      !.v_memo_chunks[i].chunk = pruned_chunk,
                                                      !.pruned[i] = 1 ]
                                ELSE /\ TRUE
                                     /\ UNCHANGED new_tx
                          /\ i' = i + 1
                          /\ blockchain' = ((blockchain \ {tx_}) \cup {new_tx'})
                          /\ tx_' = new_tx'
                          /\ pc' = [pc EXCEPT !["NODE"] = "PruneChunks"]
                     ELSE /\ pc' = [pc EXCEPT !["NODE"] = "UpdateTx"]
                          /\ UNCHANGED << blockchain, tx_, new_tx, i >>
               /\ UNCHANGED << txPool, memo_key, salt, decrypted_memo, 
                               encryption_key, plaintext_memo_chunks, 
                               encrypted_memo_chunks, tx_v6, tx >>

UpdateTx == /\ pc["NODE"] = "UpdateTx"
            /\ new_tx' = [ tx_ EXCEPT
                             !.f_all_pruned = TRUE,
                             !.salt_or_hash = RandomHash(32)
                         ]
            /\ blockchain' = ((blockchain \ {tx_}) \cup {new_tx'})
            /\ tx_' = new_tx'
            /\ pc' = [pc EXCEPT !["NODE"] = "Done"]
            /\ UNCHANGED << txPool, memo_key, salt, decrypted_memo, 
                            encryption_key, plaintext_memo_chunks, 
                            encrypted_memo_chunks, tx_v6, i, tx >>

Node == ValidateTx \/ PruneChunks \/ UpdateTx

Scan == /\ pc["SCANNER"] = "Scan"
        /\ Cardinality(blockchain) > 0
        /\ tx' = (CHOOSE t \in blockchain : \E a \in t.actions : a.receiver = "USER")
        /\ pc' = [pc EXCEPT !["SCANNER"] = "Decrypt"]
        /\ UNCHANGED << txPool, blockchain, memo_key, salt, decrypted_memo, 
                        encryption_key, plaintext_memo_chunks, 
                        encrypted_memo_chunks, tx_v6, tx_, new_tx, i >>

Decrypt == /\ pc["SCANNER"] = "Decrypt"
           /\ decrypted_memo' = DecryptedMemoFinal(DecryptMemo(memo_key, tx.salt_or_hash, tx.v_memo_chunks))
           /\ IF tx.f_all_pruned = TRUE
                 THEN /\ Assert(decrypted_memo' = (pruned_chunk \o pruned_chunk), 
                                "Failure of assertion at line 161, column 13.")
                 ELSE /\ TRUE
           /\ pc' = [pc EXCEPT !["SCANNER"] = "Done"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                           plaintext_memo_chunks, encrypted_memo_chunks, tx_v6, 
                           tx_, new_tx, i, tx >>

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
