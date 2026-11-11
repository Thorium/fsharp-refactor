# Builds and packages the VS Code companion extension. Cross-platform
# (pwsh on Linux CI works): stages the analyzers, stamps the
# version from Directory.Build.props, compiles the TypeScript, and runs
# vsce package.
#
#     pwsh -File CreateVsCodeVsix.ps1
#     code --install-extension artifacts/fsharp-refactor-<version>.vsix
param([string]$Configuration = "Release")

$ErrorActionPreference = "Stop"
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$repo = Resolve-Path (Join-Path $here "../..")

dotnet build (Join-Path $repo "src/FSharp.Refactor.Analyzers") -c $Configuration
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

$analyzerDir = Join-Path $here "analyzers"
if (Test-Path $analyzerDir) { Remove-Item -Recurse -Force $analyzerDir }
New-Item -ItemType Directory -Force $analyzerDir | Out-Null
Copy-Item (Join-Path $repo "src/FSharp.Refactor.Analyzers/bin/$Configuration/net10.0/FSharp.Refactor.Analyzers.dll") $analyzerDir
Copy-Item (Join-Path $repo "icon.png") $here -Force
Copy-Item (Join-Path $repo "LICENSE") $here -Force

# ONE version source, same as the vsix and the nupkgs
$repoVersion = [regex]::Match(
    [IO.File]::ReadAllText((Join-Path $repo "Directory.Build.props")),
    '<Version>([^<]+)</Version>').Groups[1].Value
$packageJsonPath = Join-Path $here "package.json"
$packageJson = [IO.File]::ReadAllText($packageJsonPath)
$packageJson = $packageJson -replace '("version":\s*")[^"]+(")', "`${1}$repoVersion`${2}"
# what the Status command reports: the analyzers' version and when this
# package was built, read back from package.json at runtime
$built = (Get-Date).ToUniversalTime().ToString("yyyy-MM-dd HH:mm") + " UTC"
$packageJson = $packageJson -replace '("analyzers":\s*")[^"]*(")', "`${1}$repoVersion`${2}"
$packageJson = $packageJson -replace '("built":\s*")[^"]*(")', "`${1}$built`${2}"
# the analyzer SDK the staged build targets, as major.minor: the extension
# checks the FsAutoComplete Ionide runs against it
$sdkPin = [regex]::Match(
    [IO.File]::ReadAllText((Join-Path $repo "src/FSharp.Refactor.Analyzers/FSharp.Refactor.Analyzers.fsproj")),
    'FSharp\.Analyzers\.SDK" Version="(\d+)\.(\d+)')
$sdks = "$($sdkPin.Groups[1].Value).$($sdkPin.Groups[2].Value)"
$packageJson = $packageJson -replace '("sdks":\s*")[^"]*(")', "`${1}$sdks`${2}"
[IO.File]::WriteAllText($packageJsonPath, $packageJson)
Write-Host "Stamped VS Code extension version $repoVersion (built $built)"

Push-Location $here
try {
    npm install --no-audit --no-fund
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    npm run compile
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

    # the file is named after the extension's own id, so the package name
    # and the marketplace identity can never drift apart
    $extensionName = [regex]::Match($packageJson, '"name":\s*"([^"]+)"').Groups[1].Value
    $artifacts = Join-Path $here "artifacts"
    New-Item -ItemType Directory -Force $artifacts | Out-Null
    $output = Join-Path $artifacts "$extensionName-$repoVersion.vsix"
    npx vsce package --out $output
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    Write-Host "Created $output"
}
finally {
    Pop-Location
}
