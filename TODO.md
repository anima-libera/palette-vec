
-----------------------------

# Features

## Implement nice traits
(look at std `Vec` and `HashMap` to get inspiration for nice combinations of type parameters and `Self` as reference or not)
- `Debug`, `Default`, `PartialEq`, `Eq`, `Hash`
- `Index` (for one index but also ranges)
- `Extend`, `FromIterator`, `IntoIterator`, `From` (like from `Vec<T>`, `[T]` and the likes)
- serde traits: `Serialize`, `Deserialize`

## Implement nice methods
(look at std `Vec` and `HashMap` to get inspiration)
- `with_len_and_palette_len` (which preallocates the palette and starts with the good keys size)
- `with_capacity`, `capacity`, `reserve`
- unsafe unstable `into_raw_parts` and `from_raw_parts`
- is an element an outlier or a common element
- get iterators over various combinations of palette data
- insert and remove values at arbitrary indices
- `concat`, `reverse`
- `fill`, `fill_with`, `clone_from_slice` (and `copy_from_slice`)
- `copy_within`, `swap`, `swap` but a range with a range, unsafe `swap_unchecked`
- unsafe `get_unchecked`
- unsafe `get_mut` (unsafe because it impacts all instances, also what if it becomes equaly to an other palette entry) and `get_mut_unchecked`
- `iter`, `windows`, `chunks`
- `drain`
- `clear`
- `set_multiple`, etc.

## Macros
Something like `palvec![elem; N]` and `palvec![elem, elem, elem, ...]`.
And the same for `outpalvec![...]`.

## Add PalVecSlice and OutPalVecSlice types
They would be views into a range (that can be `..`) of an owned PalVec.

## Allow for multiple PalVecs to share a single palette (or not?)
Maybee... This would be tricky to make it work safely without a super annoying API, and also the use cases seem even more niche than palette compression...

## Multithreading
Allow some safe multithreaded operations on PalVecs.
For example, it would be nice to allow for multiple threads to each be able to iterate (mutably) over non-overlapping slices. It would require a thread-safe mutable palette with special care for performance (like trying to lock as few as possible), and be careful at the slice edges where memory words are shared by two slices (like `...[xxxy][yyzz]...` where x, y and z are keys and memory words are in brackets, if a slice starts or stops at y (included) then it will share a memory word with its neighboring slice) that will require care to be handled by multiple threads without data races.

## Tests
Test everything, stress test everything, with all the types and settings.
WIP

## Benchmarks
Make benchmarks of performance and memory usage of Vec, PalVec and OutPalVec in various stress tests.
WIP

## Documentation and examples
- Explain the usecases of palette compression, large arrays of few different values that would even be potentially big, and in practice: chunks of a 3D/4D voxel world (Minecraft does it), large voxel scenes, chunks of a 2D powder game with a large map, the large grid of a 2D/3D celular automata, some other specific needs (such as a large ordered list of words/whatever that should be read and written fast but without much insertion/removals), etc.
- Explain why the outliers optimization is so cool, with the example of voxel game chunks (lots of air, stone, dirt, grass, and very few very diverse other kinds of blocks like torches, flowers, chests, etc. that could all be sorted into one outlier key to reduce the size of keys in the key vec).
- Explain how the outliers optimization works, with figures and everything.
- Document every single public type and method and module and everything (extensively when necessary).

-----------------------------

# Optimisations and optimization-related features

## Reverse hash map (BAD, see "Fast adders" instead!)
When `get` or `pop` are called, we look the key at a given index and then index the palette with the key we got, index the palette with a key is fast. However, when `set` or `push` are called, we *index the palette with a given element* to look for the key associated with the element, and this is slow. We have to iterate over all the palette (at worst) and perform equality checks between pairs of elements multiple times which may be expensive for what we know.
What if we could have a sort of reverse hash map (if the element type is hashable) where we can lookup the key associated to a given element fast too? This would reduce the time spent iterating over the palette, but also potentially reduce the equality checks (as we mainly compare hashes). (Yeah this is literally a hash map vs a key-value unsorted vector.)
This would add memory usage on the palette, but make performances better for writing to a PalVec.

## Fast adders
Instead of a reverse hash map, what if:
Statically opt-in feature that allows to get "adders" for elements. An adder corresponds to an element and knows its key (in the PalVec it is bound to). When using `set` or `push` to add an element for which we have an adder, then we can use the adder's knowledge of the element's key to find it immediately in the palette which makes it fast (instead of the slow way of iterating thorugh the palette and checking for equality with each palette entry element). We have to make sure that the adder's key is updated (or at least invalidated) when the element's key changes.

## Reverse hash map but good
Instead of fast adders, what if:
Small compile-time sized circular buffer that caches pairs of hash and key for elements?

## Shrinking
Add methods to shrink the allocations and use smaller keys to reduce memory usage.

## More IndexMap variants
Currently we have a (16,16), a (32,32) and a (64,64) variant (where the first number is the number of bits for the index, and the second number is the number of bits for the OPSK). This is so that we deal with entries that are properly aligned in memory and that we do not resize too often.
But what about entries such as (10,6), (50,14), that kind of stuff? These are aligned, and it is not as if we need super epic bit operations to extract the values either.
We could even make the index map have a runtime parameter that describes the number of bits used by OPSKs (the rest is used by the index), that can be made higer if higher OPSKs are used.

## KeyVec with branchless number access shenanigans
Capping the keys in `u32` (instead of `uszize`) and putting two adjacent `u32`s in the internal vec of the KeyVec together to make a `u64` to use branchlessly to get/set the key. This works (i've done it in an other implementation i swear), but it should be bechmarked againts the cirrent bitvec-based implementation.

## OutPalVec generic parameter to cap the IndexMap length
The fear of having the IndexMap left unbounded and having it silently growing to proportions that are too big to our taste is present in our hearts. Capped IndexMap means capped search time when the access hint misses, which might be good.
Maybe allow the IndexMap to be capped at a constant length, but also allow it to be capped to a proportion of the length of the OutPalVec.

## OutPalVec generic parameter to make outliers become common upon instance count threshold
Calling `perform_memory_opimization` once is better than nothing, but then if an element value was put in the outlier palette and then is being added way too much instances by the user without other calls to `perform_memory_opimization`, then the IndexMap grows too much. Having a common element become few is way less of a problem than having an outlier element become numerous (because in the first case it just makes the outlier optimization a bit less effective than its potential maximum efficiency, but in the second case can get so bad that it becomes worse than classic palette compression).

## Constant length
Add a way to tell a PalVec that it has a given length and this is it. The KeyVec can still have maybe one or two keys size growth loads of additional capacity ready in case the keys size increases, but then it must be exactly a multiple (or else there is memory that is just wasted, which doesn't serve any purpose) because the length will not change. This constant-length-property could be a type parameter (that doesn't contain the length, that can still be decided at runtime with the `with_len` constructor).

## More unsafe
Remove redundant checks, put parameter requirements and reassuring checks in `debug_assert!`s.

## Simd?
Would it even be usable on our non-bit-aligned keys?
Oh! It will surely be useful on the vec implementation of the IndexMap!
