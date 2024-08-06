# Notes

# The Plutus codebase contains a large number comments and the more important ones are in the form
# of Notes which have titles that can be referenced from elsewhere (this idea is taken from GHC).
# In order to make these easy to search and cross-reference we enforce a number of conventions,
# which are as follows.


# * Notes are comments beginning with `{- Note [<title>]` or `-- Note [<title>]`.  The
#   `{-` form is preferred, and a space is required before "Note".
#
# * A reference to a Note is of the form `Note [<title>]`.
#
# * The title of a note can be any sequence of printable characters, excluding ']' but
#  including spaces
#
# * In both definitions and references any (nonzero) number of spaces is allowed
#   before "Note" and between "Note" and "[".
#
# * No characters except spaces are allowed between "Note" and "["; in particular
#  `Note: [...]` is prohibited.
#
# * References must refer to the exact title of the relevant Note, including spaces and
#   capitalisation.
#
# * No two Notes should have the same title.
#
# * All references must refer to Notes which are defined somewhere in the codebase.
#
# * In definitions the title is allowed to contain line breaks but there must be
#   no line breaks between the start of the comment and "Note" or between "Note"
#   and "[".
#
# * In references, line breaks are allowed in the title and after "Note".  This
#   is allowed because code formatters may insert line breaks in these positions
#   automatically.
#
# * `NOTE [` and `note [` are not allowed in either definitions or references.
#
# * Definitions of Notes must be ordinary comments: Haddock comments are not allowed.
#
# * Plural references are not allowed: "See Notes [A], [B], and [C]" is
#   prohibited.  To avoid this, use a single reference to each note: "See Note
#   [A], Note [B], and Note [C]".


# This script scans a set of files whose names are supplied on the command line and will report most
# violations of the conventions.  Set `longOutput` to a non-zero value to get more information about
# the location of the problems (or use the `-l` option in the shell script which invokes the Awk
# code).

# The script is not foolproof.  For example, block comments with `--` can be problematic: an unlucky
# line break after "See" can leave `-- Note [...]` at the start of a line and it's difficult to tell
# automatically that that's not the start of a new Note.  Similarly, references to a Note in a block
# comment to the right of a block of code may confuse the script if there is a line break in the
# title, since a linear scan of the file will interpose some of the source code in the title.

# The script makes no attempt to distinguish between code and comments.  A Haskell program could
# contain `Note [1,2,3]` as a legitimate expression and the script will treat this as a reference to
# a Note.  A similar situation could also occur in a quoted string.

# Note also that if there are multiple references to "Note [XYZ]" and there's no such note then the
# script will only report one reference; it will be necessary to re-run the script to check for
# further references.

####################################################################################################

# This function looks for "Note [...]" and extracts everything between the parentheses.  It will
# work even if the two parentheses are on different lines and will modify $0 so that it starts just
# after the closing parenthesis, enabling further processing.  It will not work if "Note" is at the
# end of a line and "[" is on the next line, but later code takes care of the case when this occurs
# in a reference.  Line breaks in the title are replaced with single spaces.

function getNoteName(    title, linecount, p, t) {  # Conventional formatting for local variable names
    match ($0, /Note *\[/)
    if (RSTART == 0) { # Should not happen if getNoteName is called in the right context
        printf ("BUG: \"Note [\" not found at %s:%d\n", FILENAME, FNR) > "/dev/stderr"
        exit_now = 1
        exit 1
    }
    $0 = substr($0, RSTART+RLENGTH)  # Delete everything up to and including the first '['.

    title = ""
    linecount = 0

    while ($0 !~ /]/) {                      # The title of the note continues onto the next line
        sub (/[ \t]*$/, "")                  # Delete trailing whitespace
        title = title ? title " " $0 : $0    # Append the remaining text on this line to the title
        getline                              # Read the next line into $0
        sub (/^[ \t-]*/, "")                 # Delete initial comment characters and/or whitespace
        if (linecount++ >= 5) {              # Stop it from eating the entire file if the closing bracket is missing
            printf ("Unterminated Note title at %s:%d?\n", FILENAME, FNR) > "/dev/stderr"
            exit_now = 1                     # We need this because `exit` jumps to the END actions
            exit 1
        }
    }

    t = $0
    sub(/].*/, "", t)                        # Delete first closing bracket and everything after it
    title = title ? title " " t : t          # ... and append everything before it to the title
    p = index ($0, "]")
    $0 = substr($0, p+1)                     # Everything after the first closing bracket
    return title
}

function max(a,b) { return a>b ? a : b }

BEGIN {exitCode = 0; maybeSplitReference = 0}

# The previous line ended with "Note".  Check if this line begins with '[' preceded by spaces or
# dashes and if so, delete them and prepend "Note " so that we process it properly.  We assume that
# definitions are never split after "Note", so we don't try to deal with that case here.
maybeSplitReference && /^[- \t-]*\[/ {
    sub (/^[- \t]*/, "")
    $0 = "Note " $0
}

{ maybeSplitReference = 0 }  # We've dealt with this, so reset it unconditionally.

# Check for plural references
/(NOTES|Notes|notes) *\[/ {
    printf ("Invalid note format (no plurals allowed) at %s:%d\n ", FILENAME, FNR)
    printf ("> %s\n\n", $0)
    exitCode = 1
}

# Check that we have at least one space after "Note"
/Note\[/ {
    printf ("Invalid note format (space expected after \"Note\") at %s:%d\n", FILENAME, FNR)
    printf ("> %s\n\n", $0)
    exitCode = 1
}
# Check for invalid characters
/Note *[^ ] *\[/ { # There is a non-space (eg ":") between "Note" and "["
    printf ("Invalid note format at %s:%d\n", FILENAME, FNR)
    printf ("> %s\n\n", $0)
    exitCode = 1
}

# Check for Haddock
/(--|{-) *\| *Note *\[/  {
    printf ("Invalid note format (no Haddock allowed) at %s:%d ", FILENAME, FNR)
    printf ("> %s\n\n", $0)
    exitCode = 1
}

# Check for improper capitalisation
/(NOTE|note) *\[/ {  # We require all references to be of the form `Note [...]`
    printf ("Invalid note format (must say \"Note [...]\") at %s:%d\n", FILENAME, FNR)
    printf ("> %s\n\n", $0)
    exitCode = 1
}

# Make sure there's at least one space before "Note" in a definition
/(--|{-)Note *\[/ {
    printf ("Invalid note format (space expected before \"Note\") at %s:%d\n", FILENAME, FNR)
    printf ("> %s\n\n", $0)
    exitCode = 1
}

# Look for a definition
/(--|{-) *Note *\[/ {
    noteName = getNoteName()
    if (defined[noteName]) {
        if (longOutput) {
            printf ("Duplicate Note [%s] at %s:%d and %s", noteName, FILENAME, FNR, defined[noteName])
            printf ("> %s\n\n", $0)
        }
        else printf ("Duplicate Note [%s]\n", noteName)
    }
    defined[noteName] = FILENAME ":" FNR
    # Remember that a Note with title `noteName` has been defined and record its location in case
    # we find a duplicate later.
}

# Look for a reference: this case can fire even if we already found a definition
# on the current line, but we won't find that again because getNoteName has
# removed it by the time we get here.
/ Note *\[/ {
    while ($0 ~ /Note *\[/)   # getNoteName modifies $0, so we can find multiple references here.
        referenced[getNoteName()] = FILENAME ":" FNR
    # Remember that this Note has been referenced so that at the end we can check that it's been
    # defined somewhere.  There may be multiple references, but we only remember the location of the
    # most recent one.
}

# Reference possibly split after "Note"
/Note *$/ {
    maybeSplitReference = 1
}

END {  # Report references which refer to missing Notes.
    if (exit_now) exit exitCode

    if (longOutput) {
        for (x in referenced)   # Find the maximum width of entries in the first column
            if (!(x in defined))
                w = max(w,length(x))
        for (x in referenced)
            if (!(x in defined)) {
                printf ("Missing Note %-*s%s\n\n", w+3, "["x"]", referenced[x])
                exitCode = 1
            }
    }
    else for (x in referenced)
             if (!(x in defined)) {
                 printf ("Missing Note [%s]\n\n", x)
                 exitCode = 1
             }
    exit exitCode
}
