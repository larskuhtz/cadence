# Glossary — protocol vocabulary

*(Informal paper-reading notes; predate the 2026-07-07 revision — NOTE
the `Ev(j)` chain below is the PRE-FIX one; the shipped chain is
`⊥ → own signed entry → FastQC`, see [`ChorusDesign.md`](./ChorusDesign.md)
§7.2. The model itself is the authority on the shipped chain; this file is a
reading aid for the paper's notation.)*

`s`: slot
`j`: propose index
`ρ`: MerkleRoot (for a proposer)

`r`: validator index (chunk index)
`d_r`: chunk data
`π_r`: chunk inclusion proof.

`Entry(j)` [ProposalRoot]: `⟨s, j, ρ⟩`
`ChunkHeader` [proposer signed entry]: `⟨s, j, ρ, Sign_j(⟨s, j, ρ⟩)⟩`

Chunk [Chunk Message]: `⟨CHUNK, ChunkHeader, r, d_r, π_r⟩`

`Ev(j)` [Evidence]:
  - `⊥` -> `fallbakck signed entry` -> `FallbackQC` -> `EquivCert` -> `FastQC`.

`SignedEntries` (for validator i):
  - `{⟨Entry(j), Sign_i(⟨Vote, Etnry(j)⟩)}_{j is Proposer}`

`DecryptShare`: decryption share for slot s and validator i

vote message: `⟨VOTE, s, SignedEntries, Chunks, DecryptShare⟩`


## Module 7

State:
- `Entry(j)`

## Module 8

State:
- `Ev(j)`: stronges evidence about `j`
   - `⊥` -> `fallbakck signed entry` -> `FallbackQC` -> `EquivCert` -> `FastQC`.

## Module 9

State:
- `Ev(j)`: see module 8
- `M_i`: Fallback vote messages

# Questions:

- Clarify terminology around ChunkHeader, Entry, and SignedEntry.
- Why is `onChunkValidated` defined in Module 7 when it is used only in Module 10?
- Why is ρ_⊥ named this way? It's value can be ⊥, but it can also be something
  else.