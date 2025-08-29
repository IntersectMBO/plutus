---
sidebar_position: 1
---

# Builtin Arrays

:::danger Upcoming Feature
**This is an upcoming feature that is not yet available for use.** The `BuiltinArray` type and related functions are currently under development and will be included in a future version of Plutus. This documentation is provided for preview purposes only.
:::

For multiple lookups by index, `BuiltinArray` provides significantly better performance than lists. The key advantage is in the lookup operations themselves.

**Lookup Performance Comparison:**
A single lookup at index 99 of a 100-element data structure shows that the CPU cost for lookup on a standard Plinth list (`[Integer]`, a sum-of-products type) is **206 times higher** than on a `BuiltinArray`.

**Important Considerations:**
Currently, `BuiltinArray` creation is implemented as conversion from lists, which involves traversing the entire list. This conversion cost should be factored into your performance calculations - the dramatic lookup performance improvement needs to be amortized over multiple lookups to justify the conversion overhead.

As a rule of thumb, if you only need to perform a single lookup, the conversion cost may not be worthwhile. The benefits become apparent when performing several lookups on the same data structure.

**Future Development:**
In future language versions, arrays are planned to be added to the `Data`-encoded `ScriptContext` precisely to avoid these high conversion costs, allowing arrays to be provided directly without requiring conversion from lists.

## Choosing Arrays vs Lists

When designing your data structures, consider your access patterns:

**Choose arrays when:**
- You need multiple index-based lookups (e.g., `arr[42]`, `arr[17]`)
- Your access pattern is primarily random access rather than sequential
- The data structure size is relatively stable after creation
- You're building lookup tables or similar structures

**Choose lists when:**
- You primarily need sequential access (head/tail operations, pattern matching)
- You frequently prepend elements (`:` operator)
- Your access pattern is mostly single-pass iteration
- You're following functional programming patterns that work naturally with lists

**Current limitations:**
Note that you can't always choose arrays "from the start" because data often comes from external sources as lists (like elements in `ScriptContext`). This is why the conversion scenario is currently common, and why future versions plan to provide arrays directly in these contexts.

Functions for working with `BuiltinArray` are available in the `PlutusTx.Builtins` module:

```haskell
import PlutusTx.Builtins 
  ( BuiltinArray
  , indexArray
  , listToArray
  , lengthOfArray
  )
```

<details>
  <summary>Lookup comparison: SOP List vs. BuiltinList vs. BuiltinArray</summary>
  <LiteralInclude file="Example/Builtin/Array/Main.hs" language="haskell" />
  
  Result of the evaluation:
  ![BuiltinArray Performance Comparison](/code/Example/Builtin/Array/Screenshot.png)
</details>
