module PlutusCore.Pretty.ConfigName
    ( PrettyConfigName (..)
    , HasPrettyConfigName (..)
    , defPrettyConfigName
    , debugPrettyConfigName
    ) where

{- Note [PLC names pretty-printing]
UPDATE: We no longer have such fancy names that this note describes.
However it's still nice to have a working boileplate-free solution for sophisticated cases.

There are several possible designs on how to pretty-print PLC names. We choose the simplest one
which leads to less boilerplate on the implementation side and more concise API. The trade-off is
that it's completely inextensible and the pretty-printer configuration for PLC names is hardcoded
to 'PrettyConfigName'. Originally I tried to do a clever thing and allow different pretty-printer
configs for PLC names, but it turned out to be very complicated and the API would make users unhappy.
We may try to improve the current design later, but for now it works fine.

Here is how the current design is motivated:

Consider the 'PrettyConfigClassic' class

    newtype PrettyConfigClassic configName = PrettyConfigClassic
        { _pccConfigName :: configName
        }

(which only specifies how to print a PLC name) and this hypothethical instance:

    instance PrettyBy configName (tyname a) =>
            PrettyBy (PrettyConfigClassic configName) (Type tyname a)

which determines how to pretty-print a 'Type' provided you know how to pretty-print a @tyname a@
by a 'configName'. "Makes sense" you might think, but our names are tricky:

    newtype TyNameWithKind a = TyNameWithKind { unTyNameWithKind :: TyName (a, Kind a) }

Here in order to pretty-print a 'TyNameWithKind', 'configName' must specify how to pretty-print
a 'Kind'. And there are at least two strategies to pretty-print a 'Kind': 'Classic' and 'Refined'.
I.e. 'configName' must specify not only a 'PrettyConfigName', but also a strategy to
pretty-print any PLC entity because this can be required in order to pretty-print a name.
Things become worse with

    type RenamedTerm a = Term TyNameWithKind NameWithType a
    newtype NameWithType a = NameWithType (Name (a, RenamedType a))

because in order to pretty-print a 'RenamedTerm' you have to provide a config that specifies
a pretty-printing strategy for 'Term' and has such 'configName' inside that specifies
a pretty-printing strategy for 'RenamedType' (because it's required in order to pretty-print
'NameWithType') which has a 'configName' that specifies a pretty-printing strategy for 'Kind'
(because it's required in order to pretty-print 'TyNameWithKind'). This is either a hell at the
type-level (completely unbearable) or a circular config at the term level which says
"whatever your level of nestedness is, I'm able to handle that".
That latter thing would look like

    data PrettyConfigPlcLoop
        = PrettyConfigPlcLoopClassic (PrettyConfigClassic PrettyConfigPlc)
        | PrettyConfigPlcLoopRefined (PrettyConfigRefined PrettyConfigPlc)

    data PrettyConfigPlc = PrettyConfigPlc
        { _prettyConfigPlcName :: PrettyConfigName
        , _prettyConfigPlcLoop :: PrettyConfigPlcLoop
        }

i.e. there is a 'PrettyConfigName' at the current level, but you can descend further and there
will be a a 'PrettyConfigName' as well. While this might work, we're not in the Inception movie
and hence we define

    instance PrettyBy (PrettyConfigClassic configName) (tyname a) =>
            PrettyBy (PrettyConfigClassic configName) (Type tyname a)

i.e. require that a @tyname a@ must be pretty-printable with the same config as an entire 'Type'.

... and immediately run into the O(n * m) number of instances problem:

    [Classic, Refined] x [Name, TyName, NameWithType, TyNameWithKind]

where @[Classic, Refined]@ are pretty-printing strategies (we can add more in future) and
@[Name, TyName, NameWithType, TyNameWithKind]@ are PLC names (we will likely add more in future).
We do not need this level of extensibility (pretty-printing names differently depending on a
pretty-printing strategy used), so we do the following twist: for any pretty-printing strategy
we require that it must contain a PLC names pretty-printing config and then define a single instance
for each of the PLC names. E.g. for 'Name' it looks like this:

    instance HasPrettyConfigName config => PrettyBy config (Name ann) where

i.e. "you can pretty-print a 'Name' using any config as long as a 'PrettyConfigName' can be
extracted from it". This results in O(n + m) number of instances, with 'HasPrettyConfigName'
instances being defined like

    instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
        toPrettyConfigName = _pccConfigName

Here we also hardcode the PLC names pretty-printing config to be 'PrettyConfigName' which sometimes
contains redundant information (e.g. to pretty-print a 'Name' the '_pcnShowsAttached' field is not
required). This is something that we may try to improve later.
-}

-- | A config that determines how to pretty-print a PLC name.
newtype PrettyConfigName = PrettyConfigName
    { _pcnShowsUnique :: Bool -- ^ Whether to show the 'Unique' of a name or not.
    }

-- | A class of configs from which a 'PrettyConfigName' can be extracted.
class HasPrettyConfigName config where
    toPrettyConfigName :: config -> PrettyConfigName

-- | The 'PrettyConfigName' used by default: print neither 'Unique's, nor name attachments.
defPrettyConfigName :: PrettyConfigName
defPrettyConfigName = PrettyConfigName False

-- | The 'PrettyConfigName' used for debugging: print 'Unique's, but not name attachments.
debugPrettyConfigName :: PrettyConfigName
debugPrettyConfigName = PrettyConfigName True
