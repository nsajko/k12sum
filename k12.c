// Copyright 2018 Neven Sajko. All rights reserved. Use of this source code is governed by
// the GNU Public License version x that can be found in the COPYING file.

// Build with: gcc -O3 '-march=native' k12.c
// gcc -S test.c -fverbose-asm -Os -o -
// gcc -O3 -ftree-vectorize -fopt-info-vec-missed

// References:
//
// * FIPS 202
//
// * KangarooTwelve: fast hashing based on Keccak-p

// TODO: restrict; alternate implementation with explicit SIMD usage, threading (also for
// doing hex encoding and output in parallel with squeezing), hardware support on ARMv8

#ifdef NDEBUG
#	undef NDEBUG
#endif
#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum {
	// Keccak-p permutation state constants
	l = 6,
	w = 1 << l,
	b = 25 * w,

	// Sponge construction constants
	capacity = 1 << 8,
	rateBits = b - capacity,
	rateBytes = rateBits / 8,

	sha3Rounds = 24,
	k12Rounds = 12,

	k12ChunkSizeBytes = 1 << 13,

	// The number of bytes in the chaining values, also the number of bytes in the sponge capacity.
	k12ChainValBytes = capacity / 8,

	// Arbitrary tunable constants, unrelated to the Keccak algorithms.
	sha3InBufInitSize = 1 << 16,
	k12ChunkNumberGuess = 1 << 4,
	stdioBufSize = 1 << 20,
};

typedef union {
	unsigned char a[b / 8];
	uint64_t b[5][5];
} keccakSpongePermutationState;

static inline uint64_t
rol64(uint64_t a, unsigned n) {
	n %= 64;
	return (a << n) | (a >> ((64 - n) % 64));
}

static void
keccakPermutation(keccakSpongePermutationState *lanes, int rounds) {
	unsigned char R = 1;
	int round, j, x, y, t;
	for (round = 0; round < 12 + 2 * l - rounds; round++) {
		for (j = 0; j < 7; j++) {
			R = ((R << 1) ^ ((R >> 7) * 0x71U));
		}
	}
	for (; round < 12 + 2 * l; round++) {
		// Step mappings:

		// Theta
		uint64_t C[5];
		for (x = 0; x < 5; x++) {
			C[x] = lanes->b[0][x] ^ lanes->b[1][x] ^ lanes->b[2][x] ^
			       lanes->b[3][x] ^ lanes->b[4][x];
		}
		for (x = 0; x < 5; x++) {
			uint64_t tmp = C[(x + 4) % 5] ^ rol64(C[(x + 1) % 5], 1);
			for (y = 0; y < 5; y++) {
				lanes->b[y][x] ^= tmp;
			}
		}

		// Rho, Pi
		x = 1;
		y = 0;
		uint64_t current = lanes->b[y][x];
		for (t = 0; t < 24; t++) {
			j = y;
			y = (2 * x + 3 * y) % 5;
			x = j;

			uint64_t J = lanes->b[y][x];
			lanes->b[y][x] =
				rol64(current, ((unsigned)t + 1) * ((unsigned)t + 2) / 2);
			current = J;
		}

		// Chi
		for (y = 0; y < 5; y++) {
			for (x = 0; x < 5; x++) {
				C[x] = lanes->b[y][x];
			}
			for (x = 0; x < 5; x++) {
				lanes->b[y][x] ^= ~C[(x + 1) % 5] & C[(x + 2) % 5];
			}
		}

		// Iota
		for (j = 0; j < 7; j++) {
			R = ((R << 1) ^ ((R >> 7) * 0x71U));
			if ((R & 2) != 0) {
				lanes->b[0][0] ^= (1UL << ((1UL << j) - 1UL));
			}
		}
	}
}

static void
keccakSponge(const unsigned char *in, size_t inLen, int rounds, unsigned char delimSuffix,
	     size_t outLen, unsigned char *out) {
	keccakSpongePermutationState state = {.a = {0}};
	static_assert(sizeof(state.a) == sizeof(state.b), "Adjustment needed.");

	// Absorb
	int i;
	for (; rateBytes <= inLen; inLen -= rateBytes) {
		for (i = 0; i < rateBytes; i++) {
			state.a[i] ^= in[i];
		}
		keccakPermutation(&state, rounds);
		in = &(in[rateBytes]);
	}
	for (i = 0; (size_t)i < inLen; i++) {
		state.a[i] ^= in[i];
	}
	state.a[inLen] ^= delimSuffix;
	state.a[rateBytes - 1] ^= 0x80;
	keccakPermutation(&state, rounds);

	// Squeeze
	for (; rateBytes < outLen; outLen -= rateBytes) {
		memcpy(out, &state, rateBytes);
		out = &(out[rateBytes]);
		keccakPermutation(&state, rounds);
	}
	memcpy(out, &state, outLen);
}

static inline size_t
hexEncodedLen(size_t n) {
	return 2 * n;
}

static inline void
hexEncode(const unsigned char *in, size_t len, char *out) {
	const char chrs[16] = {'0', '1', '2', '3', '4', '5', '6', '7',
			       '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'};
	size_t i;
	for (i = 0; i < len; i++) {
		out[2 * i + 0] = chrs[in[i] >> 4];
		out[2 * i + 1] = chrs[in[i] & 0x0f];
	}
}

static inline void
shake128(FILE *inMsg, size_t outLen) {
	char *hexBuf = malloc(hexEncodedLen(outLen));
	if (hexBuf == NULL) {
		assert(0 != 0);
	}

	unsigned char *outBuf = malloc(outLen);
	if (outBuf == NULL) {
		free(hexBuf);
		assert(0 != 0);
	}

	unsigned char *inBuf = malloc(sha3InBufInitSize);
	if (inBuf == NULL) {
		free(outBuf);
		free(hexBuf);
		assert(0 != 0);
	}

	size_t inLen = 0, n, m = sha3InBufInitSize;
	for (;;) {
		n = fread(&(inBuf[inLen]), 1, m - inLen, inMsg);
		inLen += n;
		if (n != m - inLen) {
			break;
		}
		m <<= 1;
		inBuf = realloc(inBuf, m);
	}

	if (ferror(inMsg)) {
		free(inBuf);
		free(outBuf);
		free(hexBuf);
		assert(0 != 0);
	}

	keccakSponge(inBuf, inLen, sha3Rounds, 0x1f, outLen, outBuf);

	hexEncode(outBuf, outLen, hexBuf);
	fwrite(hexBuf, hexEncodedLen(outLen), 1, stdout);
	fputc('\n', stdout);

	free(inBuf);
	free(outBuf);
	free(hexBuf);
}

static inline int
byteLength(size_t n) {
	int i = 0;
	for (; n != 0; n >>= 8) {
		i++;
	}
	return i;
}

static inline unsigned char
lengthEncode(size_t n, int nBytes, int maxOutput, unsigned char *out) {
	int i;
	for (i = 0; i != nBytes && i != maxOutput; i++) {
		out[i] = (n >> ((nBytes - 1 - i) * 8)) & 0xff;
	}
	return (unsigned char)i;
}

static inline size_t
k12FinalNodeSize(size_t chunks) {
	return k12ChunkSizeBytes + 8 + k12ChainValBytes * chunks + (size_t)byteLength(chunks) + 1 +
	       2;
}

static inline size_t
ceilDiv(size_t n, size_t m) {
	return (n - 1) / m + 1;
}

static inline void
k12(FILE *inMsg, const char *custStr, size_t custStrLen, size_t outLen) {
	// Load and process inMsg in chunks, instead of copying the whole input file into
	// memory right away.

	char *hexBuf = malloc(hexEncodedLen(outLen));
	if (hexBuf == NULL) {
		assert(0 != 0);
	}

	unsigned char *outBuf = malloc(outLen);
	if (outBuf == NULL) {
		free(hexBuf);
		assert(0 != 0);
	}

	unsigned char *chunk = malloc(k12ChunkSizeBytes);
	if (chunk == NULL) {
		free(outBuf);
		free(hexBuf);
		assert(0 != 0);
	}

	int n = fread(chunk, 1, k12ChunkSizeBytes, inMsg);

	int custStrLenByteLength = byteLength(custStrLen);

	// Length of the string together with the length of its length encoding.
	size_t custStrFullLen = custStrLen + (size_t)custStrLenByteLength + 1UL;
	assert(custStrLen < custStrFullLen);

	// If there would be just one chunk, just hash it and return.
	if ((size_t)n + custStrFullLen <= k12ChunkSizeBytes) {
		if (ferror(inMsg)) {
			free(chunk);
			assert(0 != 0);
		}

		memcpy(&(chunk[n]), custStr, custStrLen);
		chunk[(size_t)n + custStrFullLen - 1] =
			lengthEncode(custStrLen, custStrLenByteLength, -1, &(chunk[(size_t)n + custStrLen]));
		keccakSponge(chunk, (size_t)n + custStrFullLen, k12Rounds, 0x07, outLen, outBuf);
		goto finish;
	}

	unsigned char *finalNode;
	size_t finalNodeSize;
	int m;
	long i;

	if (n != k12ChunkSizeBytes) {
		if (ferror(inMsg)) {
			free(chunk);
			free(outBuf);
			free(hexBuf);
			assert(0 != 0);
		}

		finalNodeSize = k12FinalNodeSize(ceilDiv((size_t)n + custStrFullLen - k12ChunkSizeBytes, k12ChunkSizeBytes));
		finalNode = malloc(finalNodeSize);
		memcpy(finalNode, chunk, n);
		size_t min = custStrLen;
		if (k12ChunkSizeBytes - (size_t)n < min) {
			min = k12ChunkSizeBytes - (size_t)n;
		}
		memcpy(&(finalNode[n]), custStr, min);
		n += min;
		int M = lengthEncode(custStrLen, custStrLenByteLength, k12ChunkSizeBytes - n, &(finalNode[n]));

		finalNode[k12ChunkSizeBytes] = 0x03;
		memset(&(finalNode[k12ChunkSizeBytes + 1]), 0x00, 7);

		size_t custStrLenTmp = custStrLen - min;
		custStr = &(custStr[min]);
		for (i = 0; k12ChunkSizeBytes <= custStrLenTmp; i++) {
			memcpy(chunk, custStr, k12ChunkSizeBytes);
			custStrLenTmp -= k12ChunkSizeBytes;
			custStr = &(custStr[k12ChunkSizeBytes]);
			keccakSponge(
				chunk, k12ChunkSizeBytes, k12Rounds, 0x0b, k12ChainValBytes,
				&(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
		}
		memcpy(chunk, custStr, custStrLenTmp);
		n = custStrLenTmp;

		m = lengthEncode(custStrLen, custStrLenByteLength - M, k12ChunkSizeBytes - n, &(chunk[n]));
		n += m;
		m += M;

		goto fini;
	}

	long chunkCapacity = k12ChunkNumberGuess;
	finalNode = malloc(k12FinalNodeSize(chunkCapacity));
	memcpy(finalNode, chunk, k12ChunkSizeBytes);

	finalNode[k12ChunkSizeBytes] = 0x03;
	memset(&(finalNode[k12ChunkSizeBytes + 1]), 0x00, 7);

	for (i = 0;; i++) {
		n = fread(chunk, 1, k12ChunkSizeBytes, inMsg);
		if (n != k12ChunkSizeBytes) {
			if (ferror(inMsg)) {
				free(finalNode);
				free(chunk);
				free(outBuf);
				free(hexBuf);
				assert(0 != 0);
			}
			break;
		}
		if (chunkCapacity == i) {
			chunkCapacity <<= 1;
			finalNode = realloc(finalNode, k12FinalNodeSize(chunkCapacity));
		}
		keccakSponge(chunk, k12ChunkSizeBytes, k12Rounds, 0x0b, k12ChainValBytes,
			     &(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
	}

	// Ensure finalNode is finally large enough.
	finalNodeSize = k12FinalNodeSize(i + ceilDiv((size_t)n + custStrFullLen, k12ChunkSizeBytes));
	finalNode = realloc(finalNode, finalNodeSize);

	if (k12ChunkSizeBytes - (size_t)n <= custStrLen) {
		memcpy(&(chunk[n]), custStr, k12ChunkSizeBytes - n);
		size_t custStrLenTmp = custStrLen - k12ChunkSizeBytes + (size_t)n;
		custStr = &(custStr[k12ChunkSizeBytes - n]);
		keccakSponge(chunk, k12ChunkSizeBytes, k12Rounds, 0x0b, k12ChainValBytes,
			     &(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
		i++;
		for (; k12ChunkSizeBytes <= custStrLenTmp; i++) {
			memcpy(chunk, custStr, k12ChunkSizeBytes);
			custStrLenTmp -= k12ChunkSizeBytes;
			custStr = &(custStr[k12ChunkSizeBytes]);
			keccakSponge(
				chunk, k12ChunkSizeBytes, k12Rounds, 0x0b, k12ChainValBytes,
				&(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
		}
		memcpy(chunk, custStr, custStrLenTmp);
		n = custStrLenTmp;
	} else {
		memcpy(&(chunk[n]), custStr, custStrLen);
		n += custStrLen;
	}
	m = lengthEncode(custStrLen, custStrLenByteLength, k12ChunkSizeBytes - n, &(chunk[n]));
	n += m;
fini:
	if (n == k12ChunkSizeBytes) {
		keccakSponge(chunk, k12ChunkSizeBytes, k12Rounds, 0x0b, k12ChainValBytes,
			     &(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
		i++;
		n = lengthEncode(custStrLen, custStrLenByteLength - m, -1, chunk);
		m += n;
	}
	static_assert(sizeof(size_t) < k12ChunkSizeBytes,
		      "This should not ever have happened, but now an adjustment is "
		      "needed.");
	chunk[n] = (unsigned char)m;
	keccakSponge(chunk, n + 1, k12Rounds, 0x0b, k12ChainValBytes,
		     &(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
	i++;

	finalNode[finalNodeSize - 2 - 1] = lengthEncode(
		i, byteLength(i), -1, &(finalNode[k12ChunkSizeBytes + 8 + k12ChainValBytes * i]));
	memset(&(finalNode[finalNodeSize - 2]), 0xff, 2);

	keccakSponge(finalNode, finalNodeSize, k12Rounds, 0x06, outLen, outBuf);

	free(finalNode);

finish:
	hexEncode(outBuf, outLen, hexBuf);
	fwrite(hexBuf, hexEncodedLen(outLen), 1, stdout);
	fputc('\n', stdout);

	free(chunk);
	free(outBuf);
	free(hexBuf);
}

/*
static inline void
m14(FILE *inMsg, const char *custStr, long custStrLen, size_t outLen) {
}
*/

int
main(int argc, char *argv[]) {
	static char stdioBuf[stdioBufSize];
	if (0 != setvbuf(stdin, stdioBuf, _IOFBF, sizeof(stdioBuf))) {
		return 1;
	}
	//k12(stdin, "", 0, 32);
	k12(stdin, "", 0, 10032);
	//shake128(stdin, 32);
	return 0;
}
