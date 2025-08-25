#!/bin/bash

# This script removes the PlusCal translation from a TLA+ specification file.

echo $@

# Check if at least one argument is provided
if [ $# -lt 1 ]; then
    echo "Usage: $0 <tla_file>"
    exit 1
fi

FILES_MODIFIED=0

for TLA_FILE in $@ ; do

    if [ ! -f "$TLA_FILE" ]; then
        echo "Error: File '$TLA_FILE' does not exist."
        exit 1
    fi

    # Create a temporary file to store the modified content
    TEMP_FILE=$(mktemp) || { echo "Error creating temporary file"; exit 1; }

    # Remove PlusCal translation lines
    sed '/^\\\* BEGIN TRANSLATION (chksum(pcal)/,/^\\\* END TRANSLATION/d' <"$TLA_FILE" >"$TEMP_FILE"

    # Check if the sed command was successful
    if [ $? -ne 0 ]; then
        echo "Error processing file '$TLA_FILE'."
        rm "$TEMP_FILE"
        exit 1
    fi

    # Check if file contents are identical
    if cmp -s "$TLA_FILE" "$TEMP_FILE"; then
        rm $TEMP_FILE
    else
        # Move the temporary file back to the original file
        mv "$TEMP_FILE" "$TLA_FILE"
        echo "PlusCal translation removed from '$TLA_FILE'."

        FILES_MODIFIED=1
    fi
done

exit $FILES_MODIFIED
