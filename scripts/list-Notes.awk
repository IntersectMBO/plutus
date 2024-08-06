# Scan a list of files and report the titles of all of the Notes, optionally
# with the location of their definition.  If `target` is non-null, regard it as
# a pattern and report only the titles which match it.

# The `check-Notes` script enforces rules which aren't checked here, so this may
# list Notes which `check-Notes.awk` would complain about.

function getNoteName(        title, linecount, p, t) { # Conventional formatting for local variable names
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

# Look for a definition.
/- *Note *\[/ {
    noteName = getNoteName()
    if (noteName ~ target) {
        if (defined[noteName]) {
            if (longOutput) {
                printf ("WARNING: duplicate Note [%s] at %s:%d and %s", noteName, FILENAME, FNR, defined[noteName])
                printf ("%s\n", $0)
            }
            else printf ("WARNING: duplicate Note [%s]\n", noteName)
        }
        defined[noteName] = FILENAME ":" FNR
    }
}

END {
    if (exit_now) exit 1

    if (longOutput) {
        for (x in defined)   # Find maximum width of first column
            w = max(w,length(x))
        for (x in defined)
            printf ("%-*s%s\n", w+2, x, defined[x])
    }
    else {
        for (x in defined) printf ("%s\n", x)
    }
}
