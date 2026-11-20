Splattic AR — GitHub Pages minimal camera AR test

Files in this package are the minimal conservative set for loading the exported
3DGS example, the placement marker and the AR viewer. All core JS and 3DGS data
are byte-for-byte unchanged from the original export.

How to deploy:
1. Open your GitHub Pages repository.
2. Upload ALL files and the libs/ directory with their folder hierarchy intact.
   Do not upload only index.html, and do not upload the ZIP file itself.
3. Settings > Pages > Deploy from a branch > main / (root).
4. Open https://USERNAME.github.io/REPOSITORY/ using Safari on iPhone or Chrome
   on Android. Tap AR, allow camera, scan a surface, then tap the marker.
5. Internet connection is required; 8th Wall engine scripts are loaded via CDN.

What was omitted for lightweight testing:
- 3 MP3 files: no background or gesture sound effects
- ar-experience-hud-button-icon.svg: no external website HUD icon/button
- libs/ltomoe-splat-cloud-loader.js: decorative loading animation omitted;
  a CSS spinner is used instead.
- README-AR.txt (original detailed readme, kept in the original ZIP only)

To avoid missing-media fetches, scene.json was adjusted to remove the corresponding
sound and HUD settings; index.html was adjusted to stop requesting the optional
loading-animation module. The model PLY and all AR logic stay unchanged.

Note: Desktop 3D preview and full camera AR could not be verified on iPhone from
this environment. The ZIP structure / local asset references have been audited.
