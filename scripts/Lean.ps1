param(
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$LakeArguments = @('build')
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$localBin = Join-Path $projectRoot '.toolchain\lean-4.24.0-windows\bin'
if (Test-Path -LiteralPath $localBin) {
    $env:PATH = $localBin + ';' + $env:PATH
}

# Network downloads and proof checking can run as different Windows users.
# Trust only this project's dependency checkouts, for this process alone.
$packageRoot = Join-Path $projectRoot '.lake\packages'
if (Test-Path -LiteralPath $packageRoot) {
    $checkouts = @(Get-ChildItem -LiteralPath $packageRoot -Directory |
        Where-Object { Test-Path -LiteralPath (Join-Path $_.FullName '.git') })
    $env:GIT_CONFIG_COUNT = [string]$checkouts.Count
    for ($index = 0; $index -lt $checkouts.Count; $index++) {
        [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$index", 'safe.directory', 'Process')
        [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$index",
            $checkouts[$index].FullName.Replace('\', '/'), 'Process')
    }
}

Push-Location -LiteralPath $projectRoot
try {
    & lake @LakeArguments
    $result = $LASTEXITCODE
} finally {
    Pop-Location
}
exit $result
