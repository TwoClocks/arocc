// SPDX-License-Identifier: GPL-3.0-or-later

// This test file is auto-generated. do not edit.
// This file is a derivative work from the test files found
// in this repo : https://github.com/mahkoh/repr-c
// and is under the same licence as the original work.

typedef struct {
#ifdef MSVC
    int x __declspec(align(128)) ;
#else
    int x __attribute__((aligned(128)));
#endif
} A1;
A1 var1;
struct A1_extra_alignment {
    char a;
    A1 b;
};
struct A1_extra_alignment var2;
#pragma pack(1)
struct A1_extra_packed {
#ifdef MSVC
    char a[sizeof(A1)];
#else
    A1 a;
#endif
};
#pragma pack()
struct A1_extra_required_alignment {
    char a;
    struct A1_extra_packed b;
};
struct A1_extra_required_alignment var3;
struct A1_extra_size {
    char a[sizeof(A1)+1];
    char b;
};
struct A1_extra_size var4;

typedef union {
#ifdef MSVC
    int x __declspec(align(128)) ;
#else
    int x __attribute__((aligned(128)));
#endif
} A2;
A2 var5;
struct A2_extra_alignment {
    char a;
    A2 b;
};
struct A2_extra_alignment var6;
#pragma pack(1)
struct A2_extra_packed {
#ifdef MSVC
    char a[sizeof(A2)];
#else
    A2 a;
#endif
};
#pragma pack()
struct A2_extra_required_alignment {
    char a;
    struct A2_extra_packed b;
};
struct A2_extra_required_alignment var7;
struct A2_extra_size {
    char a[sizeof(A2)+1];
    char b;
};
struct A2_extra_size var8;

#ifdef MSVC
typedef int B __declspec(align(128)) ;
#else
typedef int B __attribute__((aligned(128)));
#endif
B var9;
struct B_extra_alignment {
    char a;
    B b;
};
struct B_extra_alignment var10;
#pragma pack(1)
struct B_extra_packed {
#ifdef MSVC
    char a[sizeof(B)];
#else
    B a;
#endif
};
#pragma pack()
struct B_extra_required_alignment {
    char a;
    struct B_extra_packed b;
};
struct B_extra_required_alignment var11;
struct B_extra_size {
    char a[sizeof(B)+1];
    char b;
};
struct B_extra_size var12;

typedef struct {
    B x;
} C1;
C1 var13;
struct C1_extra_alignment {
    char a;
    C1 b;
};
struct C1_extra_alignment var14;
#pragma pack(1)
struct C1_extra_packed {
#ifdef MSVC
    char a[sizeof(C1)];
#else
    C1 a;
#endif
};
#pragma pack()
struct C1_extra_required_alignment {
    char a;
    struct C1_extra_packed b;
};
struct C1_extra_required_alignment var15;
struct C1_extra_size {
    char a[sizeof(C1)+1];
    char b;
};
struct C1_extra_size var16;

typedef union {
    B x;
} C2;
C2 var17;
struct C2_extra_alignment {
    char a;
    C2 b;
};
struct C2_extra_alignment var18;
#pragma pack(1)
struct C2_extra_packed {
#ifdef MSVC
    char a[sizeof(C2)];
#else
    C2 a;
#endif
};
#pragma pack()
struct C2_extra_required_alignment {
    char a;
    struct C2_extra_packed b;
};
struct C2_extra_required_alignment var19;
struct C2_extra_size {
    char a[sizeof(C2)+1];
    char b;
};
struct C2_extra_size var20;

typedef struct {
#ifdef MSVC
    B x __declspec(align(256)) ;
#else
    B x __attribute__((aligned(256)));
#endif
} D1;
D1 var21;
struct D1_extra_alignment {
    char a;
    D1 b;
};
struct D1_extra_alignment var22;
#pragma pack(1)
struct D1_extra_packed {
#ifdef MSVC
    char a[sizeof(D1)];
#else
    D1 a;
#endif
};
#pragma pack()
struct D1_extra_required_alignment {
    char a;
    struct D1_extra_packed b;
};
struct D1_extra_required_alignment var23;
struct D1_extra_size {
    char a[sizeof(D1)+1];
    char b;
};
struct D1_extra_size var24;

typedef union {
#ifdef MSVC
    B x __declspec(align(256)) ;
#else
    B x __attribute__((aligned(256)));
#endif
} D2;
D2 var25;
struct D2_extra_alignment {
    char a;
    D2 b;
};
struct D2_extra_alignment var26;
#pragma pack(1)
struct D2_extra_packed {
#ifdef MSVC
    char a[sizeof(D2)];
#else
    D2 a;
#endif
};
#pragma pack()
struct D2_extra_required_alignment {
    char a;
    struct D2_extra_packed b;
};
struct D2_extra_required_alignment var27;
struct D2_extra_size {
    char a[sizeof(D2)+1];
    char b;
};
struct D2_extra_size var28;

typedef struct {
    B x;
#ifdef MSVC
} __declspec(align(256))  E1;
#else
} __attribute__((aligned(256))) E1;
#endif
E1 var29;
struct E1_extra_alignment {
    char a;
    E1 b;
};
struct E1_extra_alignment var30;
#pragma pack(1)
struct E1_extra_packed {
#ifdef MSVC
    char a[sizeof(E1)];
#else
    E1 a;
#endif
};
#pragma pack()
struct E1_extra_required_alignment {
    char a;
    struct E1_extra_packed b;
};
struct E1_extra_required_alignment var31;
struct E1_extra_size {
    char a[sizeof(E1)+1];
    char b;
};
struct E1_extra_size var32;

typedef union {
    B x;
#ifdef MSVC
} __declspec(align(256))  E2;
#else
} __attribute__((aligned(256))) E2;
#endif
E2 var33;
struct E2_extra_alignment {
    char a;
    E2 b;
};
struct E2_extra_alignment var34;
#pragma pack(1)
struct E2_extra_packed {
#ifdef MSVC
    char a[sizeof(E2)];
#else
    E2 a;
#endif
};
#pragma pack()
struct E2_extra_required_alignment {
    char a;
    struct E2_extra_packed b;
};
struct E2_extra_required_alignment var35;
struct E2_extra_size {
    char a[sizeof(E2)+1];
    char b;
};
struct E2_extra_size var36;

// MAPPING|ONE|aarch64-generic-macos-none:Clang|aarch64-generic-fuchsia-gnu:Clang|aarch64-generic-linux-android:Clang|aarch64-generic-freebsd-gnu:Clang|aarch64-generic-hermit-eabi:Clang|aarch64-generic-linux-gnu:Gcc|aarch64-generic-linux-musl:Gcc|aarch64-generic-netbsd-gnu:Clang|aarch64-generic-other-eabi:Clang|aarch64-generic-openbsd-gnu:Clang|aarch64-generic-ios-none:Clang|aarch64-generic-ios-macabi:Clang|aarch64-generic-tvos-none:Clang|arm-baseline-other-eabi:Clang|arm-baseline-other-eabihf:Clang|arm-baseline-linux-gnueabi:Gcc|arm-baseline-linux-gnueabihf:Gcc|arm-arm710t-linux-gnueabi:Gcc|arm-arm1020e-linux-gnueabi:Gcc|arm-arm1136j_s-freebsd-gnueabihf:Clang|arm-arm1136j_s-netbsd-eabihf:Clang|arm-baseline-other-eabi:Clang|arm-baseline-other-eabihf:Clang|arm-cortex_r4-ios-none:Clang|arm-cortex_r4-linux-android:Clang|arm-cortex_r4-other-eabi:Clang|arm-cortex_r4-other-eabihf:Clang|arm-baseline-ios-none:Clang|arm-cortex_r4-freebsd-gnueabihf:Clang|arm-cortex_r4-linux-gnueabi:Gcc|arm-cortex_r4-linux-gnueabihf:Gcc|arm-cortex_r4-netbsd-eabihf:Clang|hexagon-generic-linux-musl:Clang|i386-i386-ios-none:Clang|i386-i586-linux-gnu:Gcc|i386-i586-linux-musl:Gcc|i386-i686-macos-none:Clang|i386-i686-linux-android:Clang|i386-i686-windows-gnu:Gcc|i386-i686-freebsd-gnu:Clang|i386-i686-haiku-gnu:Clang|i386-i686-linux-gnu:Gcc|i386-i686-linux-musl:Gcc|i386-i686-netbsd-gnu:Clang|i386-i686-openbsd-gnu:Clang|mips64el-mips64-linux-gnuabi64:Gcc|mips64el-mips64-linux-musl:Gcc|mips64-mips64-linux-gnuabi64:Gcc|mips64-mips64-linux-musl:Gcc|mipsel-mips32-linux-gnu:Gcc|mipsel-mips32-linux-musl:Gcc|mipsel-mips32-other-eabi:Clang|mips-mips32-linux-gnu:Gcc|mips-mips32r6-linux-gnu:Gcc|mips-mips32-linux-gnuabi64:Gcc|mips-mips64r6-linux-gnuabi64:Gcc|mips-mips32-linux-gnu:Gcc|mips-mips32-linux-musl:Gcc|powerpc64le-ppc64le-linux-gnu:Gcc|powerpc64le-ppc64le-linux-musl:Gcc|powerpc64-ppc64-freebsd-gnu:Clang|powerpc64-ppc64-linux-gnu:Gcc|powerpc64-ppc64-linux-musl:Gcc|powerpc-ppc-linux-gnu:Gcc|powerpc-ppc-linux-musl:Gcc|powerpc-ppc-netbsd-gnu:Clang|riscv32-baseline_rv32-other-eabi:Clang|riscv32-baseline_rv32-linux-gnu:Gcc|riscv64-baseline_rv64-other-eabi:Clang|riscv64-baseline_rv64-linux-gnu:Gcc|s390x-generic-linux-gnu:Gcc|sparc64-v9-linux-gnu:Gcc|sparc64-v9-netbsd-gnu:Clang|sparc64-v9-openbsd-gnu:Clang|sparc-v8-linux-gnu:Gcc|sparc-v9-solaris-eabi:Clang|thumb-arm710t-other-eabi:Clang|thumb-cortex_m0-other-eabi:Clang|thumb-cortex_m4-other-eabihf:Clang|thumb-cortex_m4-other-eabi:Clang|thumb-sc300-other-eabi:Clang|thumb-baseline-other-eabi:Clang|thumb-cortex_m33-other-eabihf:Clang|thumb-cortex_m33-other-eabi:Clang|wasm32-generic-emscripten-musl:Clang|wasm32-generic-other-musl:Clang|wasm32-generic-wasi-musl:Clang|x86_64-x86_64-ios-macabi:Clang|x86_64-x86_64-ios-none:Clang|x86_64-x86_64-macos-none:Clang|x86_64-x86_64-tvos-none:Clang|x86_64-x86_64-other-eabi:Clang|x86_64-x86_64-fuchsia-gnu:Clang|x86_64-x86_64-linux-android:Clang|x86_64-x86_64-solaris-eabi:Clang|x86_64-x86_64-windows-gnu:Gcc|x86_64-x86_64-dragonfly-eabi:Clang|x86_64-x86_64-freebsd-gnu:Clang|x86_64-x86_64-haiku-gnu:Clang|x86_64-x86_64-hermit-eabi:Clang|x86_64-x86_64-linux-gnux32:Gcc|x86_64-x86_64-linux-gnu:Gcc|x86_64-x86_64-linux-musl:Gcc|x86_64-x86_64-netbsd-gnu:Clang|x86_64-x86_64-openbsd-gnu:Clang|END
// repr targets Aarch64AppleMacosx|Some("aarch64-generic-macos-none") Aarch64Fuchsia|Some("aarch64-generic-fuchsia-gnu") Aarch64LinuxAndroid|Some("aarch64-generic-linux-android") Aarch64UnknownFreebsd|Some("aarch64-generic-freebsd-gnu") Aarch64UnknownHermit|Some("aarch64-generic-hermit-eabi") Aarch64UnknownLinuxGnu|Some("aarch64-generic-linux-gnu") Aarch64UnknownLinuxMusl|Some("aarch64-generic-linux-musl") Aarch64UnknownNetbsd|Some("aarch64-generic-netbsd-gnu") Aarch64UnknownNone|Some("aarch64-generic-other-eabi") Aarch64UnknownOpenbsd|Some("aarch64-generic-openbsd-gnu") Aarch64UnknownRedox|None Arm64AppleIos|Some("aarch64-generic-ios-none") Arm64AppleIosMacabi|Some("aarch64-generic-ios-macabi") Arm64AppleTvos|Some("aarch64-generic-tvos-none") Armebv7rUnknownNoneEabi|Some("arm-baseline-other-eabi") Armebv7rUnknownNoneEabihf|Some("arm-baseline-other-eabihf") ArmLinuxAndroideabi|None ArmUnknownLinuxGnueabi|Some("arm-baseline-linux-gnueabi") ArmUnknownLinuxGnueabihf|Some("arm-baseline-linux-gnueabihf") Armv4tUnknownLinuxGnueabi|Some("arm-arm710t-linux-gnueabi") Armv5teUnknownLinuxGnueabi|Some("arm-arm1020e-linux-gnueabi") Armv5teUnknownLinuxUclibcgnueabi|None Armv6UnknownFreebsdGnueabihf|Some("arm-arm1136j_s-freebsd-gnueabihf") Armv6UnknownNetbsdelfEabihf|Some("arm-arm1136j_s-netbsd-eabihf") Armv7aNoneEabi|Some("arm-baseline-other-eabi") Armv7aNoneEabihf|Some("arm-baseline-other-eabihf") Armv7AppleIos|Some("arm-cortex_r4-ios-none") Armv7NoneLinuxAndroid|Some("arm-cortex_r4-linux-android") Armv7rUnknownNoneEabi|Some("arm-cortex_r4-other-eabi") Armv7rUnknownNoneEabihf|Some("arm-cortex_r4-other-eabihf") Armv7sAppleIos|Some("arm-baseline-ios-none") Armv7UnknownFreebsdGnueabihf|Some("arm-cortex_r4-freebsd-gnueabihf") Armv7UnknownLinuxGnueabi|Some("arm-cortex_r4-linux-gnueabi") Armv7UnknownLinuxGnueabihf|Some("arm-cortex_r4-linux-gnueabihf") Armv7UnknownNetbsdelfEabihf|Some("arm-cortex_r4-netbsd-eabihf") HexagonUnknownLinuxMusl|Some("hexagon-generic-linux-musl") I386AppleIos|Some("i386-i386-ios-none") I586UnknownLinuxGnu|Some("i386-i586-linux-gnu") I586UnknownLinuxMusl|Some("i386-i586-linux-musl") I686AppleMacosx|Some("i386-i686-macos-none") I686LinuxAndroid|Some("i386-i686-linux-android") I686PcWindowsGnu|Some("i386-i686-windows-gnu") I686UnknownFreebsd|Some("i386-i686-freebsd-gnu") I686UnknownHaiku|Some("i386-i686-haiku-gnu") I686UnknownLinuxGnu|Some("i386-i686-linux-gnu") I686UnknownLinuxMusl|Some("i386-i686-linux-musl") I686UnknownNetbsdelf|Some("i386-i686-netbsd-gnu") I686UnknownOpenbsd|Some("i386-i686-openbsd-gnu") Mips64elUnknownLinuxGnuabi64|Some("mips64el-mips64-linux-gnuabi64") Mips64elUnknownLinuxMusl|Some("mips64el-mips64-linux-musl") Mips64UnknownLinuxGnuabi64|Some("mips64-mips64-linux-gnuabi64") Mips64UnknownLinuxMusl|Some("mips64-mips64-linux-musl") MipselSonyPsp|None MipselUnknownLinuxGnu|Some("mipsel-mips32-linux-gnu") MipselUnknownLinuxMusl|Some("mipsel-mips32-linux-musl") MipselUnknownLinuxUclibc|None MipselUnknownNone|Some("mipsel-mips32-other-eabi") Mipsisa32r6elUnknownLinuxGnu|Some("mips-mips32-linux-gnu") Mipsisa32r6UnknownLinuxGnu|Some("mips-mips32r6-linux-gnu") Mipsisa64r6elUnknownLinuxGnuabi64|Some("mips-mips32-linux-gnuabi64") Mipsisa64r6UnknownLinuxGnuabi64|Some("mips-mips64r6-linux-gnuabi64") MipsUnknownLinuxGnu|Some("mips-mips32-linux-gnu") MipsUnknownLinuxMusl|Some("mips-mips32-linux-musl") MipsUnknownLinuxUclibc|None Powerpc64leUnknownLinuxGnu|Some("powerpc64le-ppc64le-linux-gnu") Powerpc64leUnknownLinuxMusl|Some("powerpc64le-ppc64le-linux-musl") Powerpc64UnknownFreebsd|Some("powerpc64-ppc64-freebsd-gnu") Powerpc64UnknownLinuxGnu|Some("powerpc64-ppc64-linux-gnu") Powerpc64UnknownLinuxMusl|Some("powerpc64-ppc64-linux-musl") PowerpcUnknownLinuxGnu|Some("powerpc-ppc-linux-gnu") PowerpcUnknownLinuxGnuspe|None PowerpcUnknownLinuxMusl|Some("powerpc-ppc-linux-musl") PowerpcUnknownNetbsd|Some("powerpc-ppc-netbsd-gnu") Riscv32|Some("riscv32-baseline_rv32-other-eabi") Riscv32UnknownLinuxGnu|Some("riscv32-baseline_rv32-linux-gnu") Riscv64|Some("riscv64-baseline_rv64-other-eabi") Riscv64UnknownLinuxGnu|Some("riscv64-baseline_rv64-linux-gnu") S390xUnknownLinuxGnu|Some("s390x-generic-linux-gnu") Sparc64UnknownLinuxGnu|Some("sparc64-v9-linux-gnu") Sparc64UnknownNetbsd|Some("sparc64-v9-netbsd-gnu") Sparc64UnknownOpenbsd|Some("sparc64-v9-openbsd-gnu") SparcUnknownLinuxGnu|Some("sparc-v8-linux-gnu") Sparcv9SunSolaris|Some("sparc-v9-solaris-eabi") Thumbv4tNoneEabi|Some("thumb-arm710t-other-eabi") Thumbv6mNoneEabi|Some("thumb-cortex_m0-other-eabi") Thumbv7emNoneEabihf|Some("thumb-cortex_m4-other-eabihf") Thumbv7emNoneEabi|Some("thumb-cortex_m4-other-eabi") Thumbv7mNoneEabi|Some("thumb-sc300-other-eabi") Thumbv8mBaseNoneEabi|Some("thumb-baseline-other-eabi") Thumbv8mMainNoneEabihf|Some("thumb-cortex_m33-other-eabihf") Thumbv8mMainNoneEabi|Some("thumb-cortex_m33-other-eabi") Wasm32UnknownEmscripten|Some("wasm32-generic-emscripten-musl") Wasm32UnknownUnknown|Some("wasm32-generic-other-musl") Wasm32Wasi|Some("wasm32-generic-wasi-musl") X86_64AppleIosMacabi|Some("x86_64-x86_64-ios-macabi") X86_64AppleIos|Some("x86_64-x86_64-ios-none") X86_64AppleMacosx|Some("x86_64-x86_64-macos-none") X86_64AppleTvos|Some("x86_64-x86_64-tvos-none") X86_64Elf|Some("x86_64-x86_64-other-eabi") X86_64Fuchsia|Some("x86_64-x86_64-fuchsia-gnu") X86_64LinuxAndroid|Some("x86_64-x86_64-linux-android") X86_64PcSolaris|Some("x86_64-x86_64-solaris-eabi") X86_64PcWindowsGnu|Some("x86_64-x86_64-windows-gnu") X86_64RumprunNetbsd|None X86_64UnknownDragonfly|Some("x86_64-x86_64-dragonfly-eabi") X86_64UnknownFreebsd|Some("x86_64-x86_64-freebsd-gnu") X86_64UnknownHaiku|Some("x86_64-x86_64-haiku-gnu") X86_64UnknownHermit|Some("x86_64-x86_64-hermit-eabi") X86_64UnknownL4reUclibc|None X86_64UnknownLinuxGnux32|Some("x86_64-x86_64-linux-gnux32") X86_64UnknownLinuxGnu|Some("x86_64-x86_64-linux-gnu") X86_64UnknownLinuxMusl|Some("x86_64-x86_64-linux-musl") X86_64UnknownNetbsd|Some("x86_64-x86_64-netbsd-gnu") X86_64UnknownOpenbsd|Some("x86_64-x86_64-openbsd-gnu") X86_64UnknownRedox|None 
#ifdef ONE
_Static_assert(sizeof(A1) == 128, "");
_Static_assert(_Alignof(A1) == 128, "");
_Static_assert(sizeof(struct A1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A1_extra_packed) == 1, "");
_Static_assert(sizeof(struct A1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A1_extra_size) == 130, "");
_Static_assert(_Alignof(struct A1_extra_size) == 1, "");
_Static_assert(sizeof(A2) == 128, "");
_Static_assert(_Alignof(A2) == 128, "");
_Static_assert(sizeof(struct A2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A2_extra_packed) == 1, "");
_Static_assert(sizeof(struct A2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A2_extra_size) == 130, "");
_Static_assert(_Alignof(struct A2_extra_size) == 1, "");
_Static_assert(sizeof(B) == 4, "");
_Static_assert(_Alignof(B) == 128, "");
_Static_assert(sizeof(struct B_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct B_extra_alignment) == 128, "");
_Static_assert(sizeof(struct B_extra_packed) == 4, "");
_Static_assert(_Alignof(struct B_extra_packed) == 1, "");
_Static_assert(sizeof(struct B_extra_required_alignment) == 5, "");
_Static_assert(_Alignof(struct B_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct B_extra_size) == 6, "");
_Static_assert(_Alignof(struct B_extra_size) == 1, "");
_Static_assert(sizeof(C1) == 128, "");
_Static_assert(_Alignof(C1) == 128, "");
_Static_assert(sizeof(struct C1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C1_extra_packed) == 1, "");
_Static_assert(sizeof(struct C1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C1_extra_size) == 130, "");
_Static_assert(_Alignof(struct C1_extra_size) == 1, "");
_Static_assert(sizeof(C2) == 128, "");
_Static_assert(_Alignof(C2) == 128, "");
_Static_assert(sizeof(struct C2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C2_extra_packed) == 1, "");
_Static_assert(sizeof(struct C2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C2_extra_size) == 130, "");
_Static_assert(_Alignof(struct C2_extra_size) == 1, "");
_Static_assert(sizeof(D1) == 256, "");
_Static_assert(_Alignof(D1) == 256, "");
_Static_assert(sizeof(struct D1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D1_extra_packed) == 1, "");
_Static_assert(sizeof(struct D1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D1_extra_size) == 258, "");
_Static_assert(_Alignof(struct D1_extra_size) == 1, "");
_Static_assert(sizeof(D2) == 256, "");
_Static_assert(_Alignof(D2) == 256, "");
_Static_assert(sizeof(struct D2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D2_extra_packed) == 1, "");
_Static_assert(sizeof(struct D2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D2_extra_size) == 258, "");
_Static_assert(_Alignof(struct D2_extra_size) == 1, "");
_Static_assert(sizeof(E1) == 256, "");
_Static_assert(_Alignof(E1) == 256, "");
_Static_assert(sizeof(struct E1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E1_extra_packed) == 1, "");
_Static_assert(sizeof(struct E1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E1_extra_size) == 258, "");
_Static_assert(_Alignof(struct E1_extra_size) == 1, "");
_Static_assert(sizeof(E2) == 256, "");
_Static_assert(_Alignof(E2) == 256, "");
_Static_assert(sizeof(struct E2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E2_extra_packed) == 1, "");
_Static_assert(sizeof(struct E2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E2_extra_size) == 258, "");
_Static_assert(_Alignof(struct E2_extra_size) == 1, "");
// MAPPING|TWO|aarch64-generic-windows-msvc:Msvc|i386-i586-windows-msvc:Msvc|i386-i686-windows-msvc:Msvc|i386-i686-uefi-msvc:Msvc|thumb-baseline-windows-msvc:Msvc|x86_64-x86_64-windows-msvc:Msvc|x86_64-x86_64-uefi-msvc:Msvc|END
// repr targets Aarch64PcWindowsMsvc|Some("aarch64-generic-windows-msvc") I586PcWindowsMsvc|Some("i386-i586-windows-msvc") I686PcWindowsMsvc|Some("i386-i686-windows-msvc") I686UnknownWindows|Some("i386-i686-uefi-msvc") Thumbv7aPcWindowsMsvc|Some("thumb-baseline-windows-msvc") X86_64PcWindowsMsvc|Some("x86_64-x86_64-windows-msvc") X86_64UnknownWindows|Some("x86_64-x86_64-uefi-msvc") 
#elif defined(TWO)
_Static_assert(sizeof(A1) == 128, "");
_Static_assert(_Alignof(A1) == 128, "");
_Static_assert(sizeof(struct A1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A1_extra_packed) == 1, "");
_Static_assert(sizeof(struct A1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A1_extra_size) == 130, "");
_Static_assert(_Alignof(struct A1_extra_size) == 1, "");
_Static_assert(sizeof(A2) == 128, "");
_Static_assert(_Alignof(A2) == 128, "");
_Static_assert(sizeof(struct A2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A2_extra_packed) == 1, "");
_Static_assert(sizeof(struct A2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A2_extra_size) == 130, "");
_Static_assert(_Alignof(struct A2_extra_size) == 1, "");
_Static_assert(sizeof(B) == 4, "");
_Static_assert(_Alignof(B) == 128, "");
_Static_assert(sizeof(struct B_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct B_extra_alignment) == 128, "");
_Static_assert(sizeof(struct B_extra_packed) == 4, "");
_Static_assert(_Alignof(struct B_extra_packed) == 1, "");
_Static_assert(sizeof(struct B_extra_required_alignment) == 5, "");
_Static_assert(_Alignof(struct B_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct B_extra_size) == 6, "");
_Static_assert(_Alignof(struct B_extra_size) == 1, "");
_Static_assert(sizeof(C1) == 128, "");
_Static_assert(_Alignof(C1) == 128, "");
_Static_assert(sizeof(struct C1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C1_extra_packed) == 1, "");
_Static_assert(sizeof(struct C1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C1_extra_size) == 130, "");
_Static_assert(_Alignof(struct C1_extra_size) == 1, "");
_Static_assert(sizeof(C2) == 128, "");
_Static_assert(_Alignof(C2) == 128, "");
_Static_assert(sizeof(struct C2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C2_extra_packed) == 1, "");
_Static_assert(sizeof(struct C2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C2_extra_size) == 130, "");
_Static_assert(_Alignof(struct C2_extra_size) == 1, "");
_Static_assert(sizeof(D1) == 256, "");
_Static_assert(_Alignof(D1) == 256, "");
_Static_assert(sizeof(struct D1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D1_extra_packed) == 1, "");
_Static_assert(sizeof(struct D1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D1_extra_size) == 258, "");
_Static_assert(_Alignof(struct D1_extra_size) == 1, "");
_Static_assert(sizeof(D2) == 256, "");
_Static_assert(_Alignof(D2) == 256, "");
_Static_assert(sizeof(struct D2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D2_extra_packed) == 1, "");
_Static_assert(sizeof(struct D2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D2_extra_size) == 258, "");
_Static_assert(_Alignof(struct D2_extra_size) == 1, "");
_Static_assert(sizeof(E1) == 256, "");
_Static_assert(_Alignof(E1) == 256, "");
_Static_assert(sizeof(struct E1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E1_extra_packed) == 1, "");
_Static_assert(sizeof(struct E1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E1_extra_size) == 258, "");
_Static_assert(_Alignof(struct E1_extra_size) == 1, "");
_Static_assert(sizeof(E2) == 256, "");
_Static_assert(_Alignof(E2) == 256, "");
_Static_assert(sizeof(struct E2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E2_extra_packed) == 1, "");
_Static_assert(sizeof(struct E2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E2_extra_size) == 258, "");
_Static_assert(_Alignof(struct E2_extra_size) == 1, "");
// MAPPING|THREE|avr-avr2-other-eabi:Gcc|END
// repr targets AvrUnknownUnknown|Some("avr-avr2-other-eabi") 
#elif defined(THREE)
_Static_assert(sizeof(A1) == 128, "");
_Static_assert(_Alignof(A1) == 128, "");
_Static_assert(sizeof(struct A1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A1_extra_packed) == 1, "");
_Static_assert(sizeof(struct A1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A1_extra_size) == 130, "");
_Static_assert(_Alignof(struct A1_extra_size) == 1, "");
_Static_assert(sizeof(A2) == 128, "");
_Static_assert(_Alignof(A2) == 128, "");
_Static_assert(sizeof(struct A2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A2_extra_packed) == 1, "");
_Static_assert(sizeof(struct A2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A2_extra_size) == 130, "");
_Static_assert(_Alignof(struct A2_extra_size) == 1, "");
_Static_assert(sizeof(B) == 2, "");
_Static_assert(_Alignof(B) == 128, "");
_Static_assert(sizeof(struct B_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct B_extra_alignment) == 128, "");
_Static_assert(sizeof(struct B_extra_packed) == 2, "");
_Static_assert(_Alignof(struct B_extra_packed) == 1, "");
_Static_assert(sizeof(struct B_extra_required_alignment) == 3, "");
_Static_assert(_Alignof(struct B_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct B_extra_size) == 4, "");
_Static_assert(_Alignof(struct B_extra_size) == 1, "");
_Static_assert(sizeof(C1) == 128, "");
_Static_assert(_Alignof(C1) == 128, "");
_Static_assert(sizeof(struct C1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C1_extra_packed) == 1, "");
_Static_assert(sizeof(struct C1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C1_extra_size) == 130, "");
_Static_assert(_Alignof(struct C1_extra_size) == 1, "");
_Static_assert(sizeof(C2) == 128, "");
_Static_assert(_Alignof(C2) == 128, "");
_Static_assert(sizeof(struct C2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C2_extra_packed) == 1, "");
_Static_assert(sizeof(struct C2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C2_extra_size) == 130, "");
_Static_assert(_Alignof(struct C2_extra_size) == 1, "");
_Static_assert(sizeof(D1) == 256, "");
_Static_assert(_Alignof(D1) == 256, "");
_Static_assert(sizeof(struct D1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D1_extra_packed) == 1, "");
_Static_assert(sizeof(struct D1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D1_extra_size) == 258, "");
_Static_assert(_Alignof(struct D1_extra_size) == 1, "");
_Static_assert(sizeof(D2) == 256, "");
_Static_assert(_Alignof(D2) == 256, "");
_Static_assert(sizeof(struct D2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D2_extra_packed) == 1, "");
_Static_assert(sizeof(struct D2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D2_extra_size) == 258, "");
_Static_assert(_Alignof(struct D2_extra_size) == 1, "");
_Static_assert(sizeof(E1) == 256, "");
_Static_assert(_Alignof(E1) == 256, "");
_Static_assert(sizeof(struct E1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E1_extra_packed) == 1, "");
_Static_assert(sizeof(struct E1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E1_extra_size) == 258, "");
_Static_assert(_Alignof(struct E1_extra_size) == 1, "");
_Static_assert(sizeof(E2) == 256, "");
_Static_assert(_Alignof(E2) == 256, "");
_Static_assert(sizeof(struct E2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E2_extra_packed) == 1, "");
_Static_assert(sizeof(struct E2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E2_extra_size) == 258, "");
_Static_assert(_Alignof(struct E2_extra_size) == 1, "");
// MAPPING|FOUR|msp430-msp430-other-eabi:Clang|END
// repr targets Msp430NoneElf|Some("msp430-msp430-other-eabi") 
#elif defined(FOUR)
_Static_assert(sizeof(A1) == 128, "");
_Static_assert(_Alignof(A1) == 128, "");
_Static_assert(sizeof(struct A1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A1_extra_packed) == 1, "");
_Static_assert(sizeof(struct A1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A1_extra_size) == 130, "");
_Static_assert(_Alignof(struct A1_extra_size) == 1, "");
_Static_assert(sizeof(A2) == 128, "");
_Static_assert(_Alignof(A2) == 128, "");
_Static_assert(sizeof(struct A2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct A2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct A2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct A2_extra_packed) == 1, "");
_Static_assert(sizeof(struct A2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct A2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct A2_extra_size) == 130, "");
_Static_assert(_Alignof(struct A2_extra_size) == 1, "");
_Static_assert(sizeof(B) == 2, "");
_Static_assert(_Alignof(B) == 128, "");
_Static_assert(sizeof(struct B_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct B_extra_alignment) == 128, "");
_Static_assert(sizeof(struct B_extra_packed) == 2, "");
_Static_assert(_Alignof(struct B_extra_packed) == 1, "");
_Static_assert(sizeof(struct B_extra_required_alignment) == 3, "");
_Static_assert(_Alignof(struct B_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct B_extra_size) == 4, "");
_Static_assert(_Alignof(struct B_extra_size) == 1, "");
_Static_assert(sizeof(C1) == 128, "");
_Static_assert(_Alignof(C1) == 128, "");
_Static_assert(sizeof(struct C1_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C1_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C1_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C1_extra_packed) == 1, "");
_Static_assert(sizeof(struct C1_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C1_extra_size) == 130, "");
_Static_assert(_Alignof(struct C1_extra_size) == 1, "");
_Static_assert(sizeof(C2) == 128, "");
_Static_assert(_Alignof(C2) == 128, "");
_Static_assert(sizeof(struct C2_extra_alignment) == 256, "");
_Static_assert(_Alignof(struct C2_extra_alignment) == 128, "");
_Static_assert(sizeof(struct C2_extra_packed) == 128, "");
_Static_assert(_Alignof(struct C2_extra_packed) == 1, "");
_Static_assert(sizeof(struct C2_extra_required_alignment) == 129, "");
_Static_assert(_Alignof(struct C2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct C2_extra_size) == 130, "");
_Static_assert(_Alignof(struct C2_extra_size) == 1, "");
_Static_assert(sizeof(D1) == 256, "");
_Static_assert(_Alignof(D1) == 256, "");
_Static_assert(sizeof(struct D1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D1_extra_packed) == 1, "");
_Static_assert(sizeof(struct D1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D1_extra_size) == 258, "");
_Static_assert(_Alignof(struct D1_extra_size) == 1, "");
_Static_assert(sizeof(D2) == 256, "");
_Static_assert(_Alignof(D2) == 256, "");
_Static_assert(sizeof(struct D2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct D2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct D2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct D2_extra_packed) == 1, "");
_Static_assert(sizeof(struct D2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct D2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct D2_extra_size) == 258, "");
_Static_assert(_Alignof(struct D2_extra_size) == 1, "");
_Static_assert(sizeof(E1) == 256, "");
_Static_assert(_Alignof(E1) == 256, "");
_Static_assert(sizeof(struct E1_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E1_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E1_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E1_extra_packed) == 1, "");
_Static_assert(sizeof(struct E1_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E1_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E1_extra_size) == 258, "");
_Static_assert(_Alignof(struct E1_extra_size) == 1, "");
_Static_assert(sizeof(E2) == 256, "");
_Static_assert(_Alignof(E2) == 256, "");
_Static_assert(sizeof(struct E2_extra_alignment) == 512, "");
_Static_assert(_Alignof(struct E2_extra_alignment) == 256, "");
_Static_assert(sizeof(struct E2_extra_packed) == 256, "");
_Static_assert(_Alignof(struct E2_extra_packed) == 1, "");
_Static_assert(sizeof(struct E2_extra_required_alignment) == 257, "");
_Static_assert(_Alignof(struct E2_extra_required_alignment) == 1, "");
_Static_assert(sizeof(struct E2_extra_size) == 258, "");
_Static_assert(_Alignof(struct E2_extra_size) == 1, "");
#endif
