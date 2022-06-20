#!/usr/bin/env bash

# Upload an event dump file to S3
#
# Example usage:
#   AWS_ACCESS_KEY_ID=<...> \
#     AWS_SECRET_ACCESS_KEY=<...> \
#     AWS_DEFAULT_REGION=<...> \
#     AWS_ENDPOINT_URL=https://s3.devx.iog.io \
#     S3_DUMP_DIR=s3://plutus/mainnet-event-dump/ \
#     ./scripts/upload-event-dump.sh \
#     <path_to_local_unzipped_event_dump_file_to_be_uploaded>

set -euo pipefail

DUMP_FILE_UNZIPPED=$1
DUMP_FILE_ZIPPED="${DUMP_FILE_UNZIPPED}.bz2"

set -x

if [ -f "$DUMP_FILE_UNZIPPED" ]; then
  bzip2 -9 "$DUMP_FILE_UNZIPPED"
  aws --endpoint-url "$AWS_ENDPOINT_URL" s3 cp "$DUMP_FILE_ZIPPED" "$S3_DUMP_DIR"
  rm "$DUMP_FILE_ZIPPED"
fi

DUMP_DIR=$(dirname "$DUMP_FILE_UNZIPPED")

# Clean up checkpoint (*.state) files. These files are large (> 1GB each), so we
# only keep the latest two. We keep two rather than one because of the possibility
# of a rollback.
readarray -t checkpoint_files < <(find "$DUMP_DIR" -name "*.state" | sort -r)

old_checkpoint_files=("${checkpoint_files[@]:2}")

for old_checkpoint_file in "${old_checkpoint_files[@]}"
do
  rm "$old_checkpoint_file"
done
