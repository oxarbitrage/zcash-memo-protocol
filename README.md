# NU7 Memo Bundles Specification

This repository contains a TLA⁺ specification that models a simplified version of the memo bundles functionality for NU7, as proposed in ZIP‑231. The specification illustrates how memo encryption, decryption, and pruning are performed in Orchard-style transactions.

## Overview

The specification consists of three primary processes:

- User Process:
    Encrypts a memo by splitting it into fixed-size chunks, padding and encrypting each chunk with a derived encryption key, and then building a transaction that carries:
    - The encrypted memo bundle (`v_memo_chunks`)
    - Associated metadata including the memo key and a salt (used for key derivation)

- Node Process:
    Validates transactions from the transaction pool, then progressively prunes the memo bundle. Pruning is implemented in a loop where, in each iteration, a memo chunk is replaced with a pruned digest. Once all chunks are pruned, the transaction is updated:

    - `f_all_pruned` is set to TRUE,
    - The `salt_or_hash` is updated with new random data representing an overall digest.
    - The `pruned` field is set to a bitfield where each bit is 1.

- Scanner Process:
    Scans the blockchain for transactions intended for a specific user, decrypts the memo bundle using the stored memo key and salt (or overall hash), and verifies that the decrypted memo is either the original message (if unpruned) or a partially pruned message.

**Note:**
The cryptographic functions (e.g., EncryptionKey, EncryptMemo, DecryptMemo) are abstracted for modeling purposes and do not capture the full complexity of the actual protocol.

## Files

- [protocol.tla](protocol.tla):
    Contains the main PlusCal specification for the protocol, including the User, Node, and Scanner processes.

- [operators.tla](operators.tla):
    Contains helper operators for:
    - Random hash generation and basic arithmetic operations,
    - Sequence splitting, padding, and manipulation,
    - Cryptographic abstractions for key derivation, memo encryption, decryption, and high-level memo processing.

## How to Run

- Clone the Repository:

```
git clone https://github.com/oxarbitrage/zcash-memo-protocol.git
cd zcash-memo-protocol
```

- Get the Toolbox and run TLC:

```
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
java -cp tla2tools.jar tlc2.TLC -config protocol.cfg protocol.tla
```

Alternatively, you can use the TLA+ Toolbox IDE to open the `protocol.tla` file and run the model checker from there or the [vscode extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus).

## Properties

- `DecrypedEqOrig`:
- `DecrypedEqPruned1`:
- `DecrypedEqPruned2`:
- `DecrypedEqAllPruned`:
