FROM nixos/nix

RUN nix-env -iA nixpkgs.dropbear

RUN mkdir -p /etc/dropbear # -R creates host keys in this directory
RUN passwd -d root # -B allows blank pw login
EXPOSE 22/tcp

# -F and -E make it run and log in the foreground
CMD ["dropbear", "-F", "-E", "-R", "-B"]
