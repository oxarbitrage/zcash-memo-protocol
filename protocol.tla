---- MODULE protocol ----
(***************************************************************************)
(* NU7 memo bundles specification                                          *)
(*                                                                         *)
(* This module models a simplified version of the Orchard protocol's memo  *)
(* encryption and decryption process as described in ZIP 231. It includes: *)
(* - A User process that encrypts a memo, constructs a transaction,        *)
(*   and adds it to a transaction pool.                                    *)
(* - A Node process that validates and commits transactions from the pool. *)
(* To demostrate pruning, a random chunk is pruned from the bundle.        *)
(* - A Scanner process that scans the blockchain, decrypts memo data,      *)
(* and verifies correctness.                                               *)
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
memo_chunk_size == 6
\* Representation of a pruned chunk.
pruned_chunk == << "p", "r", "u", "n", "e", "d" >>

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
        \* Then, split the memo into fixed-size chunks (with padding on the final chunk) using `SplitAndPadMemo`.
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
            pruned        |-> [ i \in 1..Len(encrypted_memo_chunks) |-> 0 ], \* a sequence of 0's indicating no chunk is pruned.
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

\* Validates, prunes, and commits transactions
fair process Node = "NODE"
variables 
    tx, 
    valid = TRUE,
    action,
    i_chosen,
    new_v_memo_chunks,
    new_pruned,
    new_tx;
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

    Prune:
        \* Choose a chunk index to prune.
        i_chosen := CHOOSE i \in DOMAIN tx.v_memo_chunks : TRUE;

        \* Build a new memo chunks sequence that replaces the chosen chunk’s "chunk" field with pruned_chunk.
        new_v_memo_chunks :=
          [ i \in DOMAIN tx.v_memo_chunks |->
              IF i = i_chosen
              THEN [ tx.v_memo_chunks[i] EXCEPT !.chunk = pruned_chunk ]
              ELSE tx.v_memo_chunks[i] ];

        \* Build a new pruned field: a sequence of bits (0 or 1) of the same domain as the memo chunks.
        new_pruned :=
          [ i \in DOMAIN tx.v_memo_chunks |-> IF i = i_chosen THEN 1 ELSE 0 ];

        \* Construct a new transaction record with the updated memo bundle and pruned flag.
        new_tx := [ tx EXCEPT !.v_memo_chunks = new_v_memo_chunks, !.pruned = new_pruned ];

        \* Update the blockchain by replacing the original transaction with the pruned version.
        blockchain := (blockchain \ {tx}) \cup {new_tx};
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
        decrypted_memo := DecryptedMemoFinal(DecryptMemo(memo_key, tx.salt_or_hash, tx.v_memo_chunks));
        \* If no pruning occurred, then decrypted_memo should equal memo.
        \* If pruning occurred (e.g., the first chunk was pruned), then decrypted_memo should equal:
        \* pruned_chunk concatenated with the remainder of memo.
        assert (decrypted_memo = memo)
               \/ (decrypted_memo = (pruned_chunk \o SubSeq(memo, memo_chunk_size+1, Len(memo))));
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a7105934" /\ chksum(tla) = "df47eb98")
\* Process variable tx of process Node at line 82 col 5 changed to tx_
\* Process variable action of process Node at line 84 col 5 changed to action_
CONSTANT defaultInitValue
VARIABLES pc, txPool, blockchain, memo_key, salt, encryption_key, 
          plaintext_memo_chunks, encrypted_memo_chunks, tx_builder, tx_, 
          valid, action_, i_chosen, new_v_memo_chunks, new_pruned, new_tx, tx, 
          decrypted_memo, action

vars == << pc, txPool, blockchain, memo_key, salt, encryption_key, 
           plaintext_memo_chunks, encrypted_memo_chunks, tx_builder, tx_, 
           valid, action_, i_chosen, new_v_memo_chunks, new_pruned, new_tx, 
           tx, decrypted_memo, action >>

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
        /\ i_chosen = defaultInitValue
        /\ new_v_memo_chunks = defaultInitValue
        /\ new_pruned = defaultInitValue
        /\ new_tx = defaultInitValue
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
                           valid, action_, i_chosen, new_v_memo_chunks, 
                           new_pruned, new_tx, tx, decrypted_memo, action >>

BuildTx == /\ pc["USER"] = "BuildTx"
           /\ tx_builder' = [
                                f_all_pruned  |-> FALSE,
                                salt_or_hash  |-> salt,
                                n_memo_chunks |-> Len(encrypted_memo_chunks),
                                pruned        |-> [ i \in 1..Len(encrypted_memo_chunks) |-> 0 ],
                                v_memo_chunks |-> encrypted_memo_chunks,
                                actions       |-> {[
                                    receiver |-> "USER",
                                    memo_key |-> memo_key
                                ]}
                            ]
           /\ pc' = [pc EXCEPT !["USER"] = "PushTx"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                           plaintext_memo_chunks, encrypted_memo_chunks, tx_, 
                           valid, action_, i_chosen, new_v_memo_chunks, 
                           new_pruned, new_tx, tx, decrypted_memo, action >>

PushTx == /\ pc["USER"] = "PushTx"
          /\ txPool = {}
          /\ txPool' = {tx_builder}
          /\ pc' = [pc EXCEPT !["USER"] = "Done"]
          /\ UNCHANGED << blockchain, memo_key, salt, encryption_key, 
                          plaintext_memo_chunks, encrypted_memo_chunks, 
                          tx_builder, tx_, valid, action_, i_chosen, 
                          new_v_memo_chunks, new_pruned, new_tx, tx, 
                          decrypted_memo, action >>

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
              /\ pc' = [pc EXCEPT !["NODE"] = "Prune"]
              /\ UNCHANGED << memo_key, salt, encryption_key, 
                              plaintext_memo_chunks, encrypted_memo_chunks, 
                              tx_builder, i_chosen, new_v_memo_chunks, 
                              new_pruned, new_tx, tx, decrypted_memo, action >>

Prune == /\ pc["NODE"] = "Prune"
         /\ i_chosen' = (CHOOSE i \in DOMAIN tx_.v_memo_chunks : TRUE)
         /\ new_v_memo_chunks' = [ i \in DOMAIN tx_.v_memo_chunks |->
                                     IF i = i_chosen'
                                     THEN [ tx_.v_memo_chunks[i] EXCEPT !.chunk = pruned_chunk ]
                                     ELSE tx_.v_memo_chunks[i] ]
         /\ new_pruned' = [ i \in DOMAIN tx_.v_memo_chunks |-> IF i = i_chosen' THEN 1 ELSE 0 ]
         /\ new_tx' = [ tx_ EXCEPT !.v_memo_chunks = new_v_memo_chunks', !.pruned = new_pruned' ]
         /\ blockchain' = ((blockchain \ {tx_}) \cup {new_tx'})
         /\ pc' = [pc EXCEPT !["NODE"] = "Done"]
         /\ UNCHANGED << txPool, memo_key, salt, encryption_key, 
                         plaintext_memo_chunks, encrypted_memo_chunks, 
                         tx_builder, tx_, valid, action_, tx, decrypted_memo, 
                         action >>

Node == ValidateTx \/ Prune

Scan == /\ pc["SCANNER"] = "Scan"
        /\ Cardinality(blockchain) > 0
        /\ tx' = (CHOOSE t \in blockchain : \E a \in t.actions : a.receiver = "USER")
        /\ pc' = [pc EXCEPT !["SCANNER"] = "Decrypt"]
        /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                        plaintext_memo_chunks, encrypted_memo_chunks, 
                        tx_builder, tx_, valid, action_, i_chosen, 
                        new_v_memo_chunks, new_pruned, new_tx, decrypted_memo, 
                        action >>

Decrypt == /\ pc["SCANNER"] = "Decrypt"
           /\ decrypted_memo' = DecryptedMemoFinal(DecryptMemo(memo_key, tx.salt_or_hash, tx.v_memo_chunks))
           /\ Assert((decrypted_memo' = memo)
                     \/ (decrypted_memo' = (pruned_chunk \o SubSeq(memo, memo_chunk_size+1, Len(memo)))), 
                     "Failure of assertion at line 146, column 9.")
           /\ pc' = [pc EXCEPT !["SCANNER"] = "Done"]
           /\ UNCHANGED << txPool, blockchain, memo_key, salt, encryption_key, 
                           plaintext_memo_chunks, encrypted_memo_chunks, 
                           tx_builder, tx_, valid, action_, i_chosen, 
                           new_v_memo_chunks, new_pruned, new_tx, tx, action >>

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
