# Runs the test suite as two processes side by side.
#
# xUnit runs test collections in parallel within one process, but every
# test that drives the tool end to end (Program.main installs the
# cross-file parser, redirects the console and changes directory:
# process-wide state) sits in the serialized "ProjectSources" collection,
# and six of those (SiblingProjectsTests, a `dotnet build` of a synthetic
# solution each) take 70 of the suite's 150 seconds on their own, after
# everything else has finished. A second PROCESS shares none of that
# state, so those six run beside the rest: ~75 seconds wall instead of
# ~150 on a 20-core machine (measured 2026-09-15).
#
#     pwsh -File tests/run-tests.ps1                # Debug
#     pwsh -File tests/run-tests.ps1 -c Release
#     pwsh -File tests/run-tests.ps1 -NoBuild
param(
    [Alias("c")] [string]$Configuration = "Debug",
    [switch]$NoBuild
)

$ErrorActionPreference = "Stop"
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$project = Join-Path $here "FSharp.Refactor.Tests"
$propertyProject = Join-Path $here "FSharp.Refactor.PropertyTests"
$slow = "FullyQualifiedName~SiblingProjectsTests"

if (-not $NoBuild) {
    dotnet build $project -c $Configuration --nologo -v q
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    dotnet build $propertyProject -c $Configuration --nologo -v q
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

$sw = [Diagnostics.Stopwatch]::StartNew()
$common = @("test", $project, "-c", $Configuration, "--no-build", "--nologo")
$rest = Start-Process -FilePath dotnet -ArgumentList ($common + @("--filter", "`"FullyQualifiedName!~SiblingProjectsTests`"")) -NoNewWindow -PassThru
$end2end = Start-Process -FilePath dotnet -ArgumentList ($common + @("--filter", "`"$slow`"")) -NoNewWindow -PassThru
# the FsCheck suite is a third process: a few seconds, beside the rest
$properties = Start-Process -FilePath dotnet -ArgumentList @("test", $propertyProject, "-c", $Configuration, "--no-build", "--nologo") -NoNewWindow -PassThru
$rest.WaitForExit()
$end2end.WaitForExit()
$properties.WaitForExit()
$sw.Stop()

Write-Host ("wall {0:n0} s" -f $sw.Elapsed.TotalSeconds)
if ($rest.ExitCode -ne 0 -or $end2end.ExitCode -ne 0 -or $properties.ExitCode -ne 0) {
    Write-Host "FAILED (rest: $($rest.ExitCode), end-to-end: $($end2end.ExitCode), properties: $($properties.ExitCode))"
    exit 1
}
