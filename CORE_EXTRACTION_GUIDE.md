# Haskell Core Extraction Guide

This guide shows you how to extract and analyze Haskell Core (intermediate representation) from your code.

## What is Haskell Core?

**Core** is GHC's intermediate language that sits between:
- **Haskell** (high-level) → **Core** (intermediate) → **STG** (low-level) → **Machine Code**

Core shows:
- Type information (already fully inferred/checked)
- Explicit lambda abstractions
- Case expressions
- Let bindings
- How patterns are desugared

## Method 1: Command Line (Quickest for Single Files)

### Get Simplified Core (most readable)
```bash
cd /Users/arina/hse/nir/moskvinPrj/checkProofs

# Dump simplified core to stdout
ghc -O -ddump-simpl -fforce-recomp your_file.hs -o /dev/null

# Save to file
ghc -O -ddump-simpl -fforce-recomp your_file.hs 2>&1 | tee core_output.txt

# Without optimization (simpler)
ghc -ddump-simpl -fforce-recomp your_file.hs -o /dev/null
```

### Get Desugared Core (before simplification)
```bash
ghc -ddump-core -fforce-recomp your_file.hs -o /dev/null

# Or save to file
ghc -ddump-core -fforce-recomp your_file.hs 2>&1 | tee core_desugared.txt
```

### Other Useful Flags
```bash
# Show all passes
ghc -v -ddump-simpl your_file.hs

# With more details
ghc -O -ddump-simpl -dsuppress-all your_file.hs

# Dump specific stages
ghc -ddump-tc        # Type checking
ghc -ddump-rename    # Renaming
ghc -ddump-rn        # Renamed syntax
ghc -ddump-opt       # After optimization
```

## Method 2: GHC API (Programmatic - What You're Doing)

I've already updated your `Main.hs` to include Core extraction. The key additions are:

### Basic Core Access
```haskell
-- Get module info which contains type things (Core-like info)
getModuleInfo (ms_mod_name ms) >>= \case
  Just modInfo -> do
    case modInfoTyThings modInfo of
      Just tyThings -> do
        liftIO $ putStrLn $ unlines $ map (showSDocUnsafe . ppr) tyThings
      Nothing -> liftIO $ putStrLn "No type things"
  Nothing -> liftIO $ putStrLn "No module info"
```

### Complete Example in Your Code
Run your program:
```bash
cd /Users/arina/hse/nir/moskvinPrj/checkProofs
cabal run checkProofs
```

This will now print:
1. Parsed AST (source syntax tree)
2. Renamed AST (after name resolution)
3. Typechecked AST (fully typed)
4. Core AST (simplified intermediate form)

## Method 3: Using External Tools

### ghc-core Tool (GUI Viewer)
```bash
# Install
cabal install ghc-core

# Use
ghc-core your_file.hs
```

This opens an interactive viewer showing Core with syntax highlighting and navigation.

## Method 4: Using Compiler Plugins

For more detailed Core analysis, you can write a GHC compiler plugin:

```haskell
{-# LANGUAGE DeriveGeneric #-}
import GHC
import GHC.Core
import GHC.Plugins

plugin :: Plugin
plugin = defaultPlugin { 
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todos = do
  return $ CoreDoPluginPass "PrintCore" printCore : todos

printCore :: ModGuts -> CoreM ModGuts
printCore guts = do
  putMsg (text "=== Core Bindings ===")
  putMsg (ppr (mg_binds guts))
  return guts
```

## Understanding Core Syntax

When you see Core output, common forms include:

```haskell
-- Let binding
let {x = expr} in body

-- Lambda (function)
\ (x :: Type) -> expr

-- Case expression
case expr of {
  Constructor -> result1;
  _ -> result2
}

-- Application
func arg1 arg2

-- Casts (type coercions)
expr `cast` (Co :: Type1 ~ Type2)
```

## Example Core Output

For a simple function:
```haskell
add x y = x + y
```

You might see Core like:
```
add :: Int -> Int -> Int
[GblId, Arity=2, NoCafRefs, Strictness=<S,1><S,1>]
add = \ (x :: Int) (y :: Int) -> ... (Plusint#) x y ...
```

## Tips

1. **Use `-ddump-simpl`** for most readable output (has optimizations applied)
2. **Use `-ddump-core`** for rawest form (before simplification passes)
3. **Add `-dsuppress-all`** to reduce noise if output is too large
4. **Pipe through `less`** for long outputs: `ghc -ddump-simpl file.hs | less`
5. **Look for type annotations** - they help understand what's happening
6. **Watch for casts** - `|> co` indicates type conversions

## Your Project Setup

Your `Main.hs` in `/Users/arina/hse/nir/moskvinPrj/checkProofs/src/Main.hs` now:
- Parses Haskell code
- Type checks it
- Extracts Core information via `modInfoTyThings`
- Pretty prints both AST and Core representations

To use it:
```bash
cd /Users/arina/hse/nir/moskvinPrj/checkProofs
cabal build
cabal run checkProofs
```

## Resources

- GHC Core Language: https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/defer_type_errors.html#defer-type-errors
- Core Notes in GHC: Look in `GHC.Core` module documentation
- "Secrets of the GHC inliner" paper - explains Core transformations

