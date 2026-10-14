<#
.SYNOPSIS
  LEAN-M2-CC-001 workstation launcher for Windows (Docker Desktop).

.DESCRIPTION
  Runs the AArch64 Linux toolchain image (Lean 4 / GNU Modula-2 / CompCert 3.18).
  All working data lives under -DataRoot (default D:\lean-m2), never on C:.

  On an ARM64 Windows machine the container runs natively.
  On an x64 machine it runs under QEMU emulation; the G0 probe BLOCKS that
  unless you pass -AllowEmulation (which records QEMU as part of the trusted base).

.EXAMPLE
  .\lean-m2.ps1 setup                       # create D:\lean-m2, pull the image
  .\lean-m2.ps1 setup -Build                # build the image locally instead (slow when emulated)
  .\lean-m2.ps1 probe                       # G0, toolchain only
  .\lean-m2.ps1 probe -Project mylib        # G0 against D:\lean-m2\work\mylib
  .\lean-m2.ps1 shell                       # interactive shell, D:\lean-m2\work mounted at /work
#>
[CmdletBinding()]
param(
  [Parameter(Position = 0, Mandatory = $true)]
  [ValidateSet('setup', 'probe', 'shell', 'info')]
  [string]$Command,

  [string]$Project = '',
  [string]$DataRoot = 'D:\lean-m2',
  [string]$Image = 'ghcr.io/snapkittyagent9nova/lean-m2-workstation:main',
  [switch]$Build,
  [switch]$AllowEmulation
)

# 'Continue': Windows PowerShell 5.1 turns native-command stderr into terminating errors under 'Stop'.
# Every docker call is checked through $LASTEXITCODE instead.
$ErrorActionPreference = 'Continue'
$RepoLeanM2 = Split-Path -Parent $PSScriptRoot      # ...\Sandbox\lean-m2

function Fail([string]$msg) { Write-Host "BLOCKED: $msg" -ForegroundColor Red; exit 1 }

# ---------- preconditions ----------
if (-not (Get-Command docker -ErrorAction SilentlyContinue)) {
  Fail 'docker not found. Install Docker Desktop (WSL 2 backend) and reopen PowerShell.'
}
docker info --format '{{.ServerVersion}}' *> $null
if ($LASTEXITCODE -ne 0) { Fail 'Docker Desktop is not running.' }

$drive = Split-Path -Qualifier $DataRoot
if (-not (Test-Path "$drive\")) { Fail "Drive $drive does not exist. Pass -DataRoot <path>." }

$Work      = Join-Path $DataRoot 'work'
$Toolchain = Join-Path $DataRoot 'elan-toolchains'
$Results   = Join-Path $DataRoot 'results'
foreach ($d in @($DataRoot, $Work, $Toolchain, $Results)) {
  if (-not (Test-Path $d)) { New-Item -ItemType Directory -Path $d | Out-Null }
}

$osArch = [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture.ToString()
if ($osArch -eq 'Arm64') { $Execution = 'native' } else { $Execution = 'emulated' }
if ($AllowEmulation) { $AllowFlag = '1' } else { $AllowFlag = '0' }

function Invoke-Container([string[]]$inner, [switch]$Interactive) {
  $dargs = @('run', '--rm', '--platform', 'linux/arm64')
  if ($Interactive) { $dargs += '-it' }
  $dargs += @(
    '-e', "LEAN_M2_EXECUTION=$Execution",
    '-e', "LEAN_M2_ALLOW_EMULATION=$AllowFlag",
    '-v', "${Work}:/work",
    '-v', "${Toolchain}:/home/builder/.elan/toolchains",
    '-v', "${Results}:/results",
    $Image
  ) + $inner
  & docker @dargs     # caller reads $LASTEXITCODE (no return value: output must stay on the console)
}

switch ($Command) {
  'info' {
    Write-Host "Host OS architecture : $osArch"
    Write-Host "Container execution  : $Execution (linux/arm64)"
    Write-Host "Data root            : $DataRoot"
    Write-Host "Image                : $Image"
    docker image inspect $Image --format 'Image digest         : {{index .RepoDigests 0}}'
  }

  'setup' {
    if ($Build) {
      Write-Host "Building $Image for linux/arm64 ($Execution). Emulated builds of Coq/CompCert take hours."
      docker build --platform linux/arm64 -t $Image -f (Join-Path $RepoLeanM2 'docker\Dockerfile') $RepoLeanM2
    } else {
      docker pull --platform linux/arm64 $Image
    }
    if ($LASTEXITCODE -ne 0) { Fail 'image build/pull failed.' }
    docker image inspect $Image --format '{{json .RepoDigests}} {{.Id}}' |
      Out-File -Encoding utf8 (Join-Path $Results 'image-identity.txt')
    Write-Host "Ready. Data root: $DataRoot  Execution: $Execution"
    if ($Execution -eq 'emulated' -and -not $AllowEmulation) {
      Write-Host 'Note: this is an x64 host. G0 will BLOCK until you re-run probe with -AllowEmulation.' -ForegroundColor Yellow
    }
  }

  'probe' {
    $stamp = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ')
    $out = "/results/g0-$stamp"
    if ($Project) {
      if (-not (Test-Path (Join-Path $Work $Project))) { Fail "Project not found: $(Join-Path $Work $Project)" }
      $target = "/work/$Project"
    } else {
      $target = '--toolchain-only'
    }
    Invoke-Container @('bash', '-c', "OUT=$out /opt/lean-m2/scripts/probe-toolchain.sh $target")
    $rc = $LASTEXITCODE
    Write-Host "G0 result: $(Join-Path $Results "g0-$stamp\g0-result.json")"
    exit $rc
  }

  'shell' {
    Invoke-Container @('bash') -Interactive
    exit $LASTEXITCODE
  }
}
