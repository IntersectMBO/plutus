/* Code from https://github.com/Zunawe/md5-c */

struct BFILE;
void md5String(char *input, uint8_t *result);
void md5Array(uint8_t *input, uint8_t *result, size_t inputlen);
void md5BFILE(struct BFILE *file, uint8_t *result);
