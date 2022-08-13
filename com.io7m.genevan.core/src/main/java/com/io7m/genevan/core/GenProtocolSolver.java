/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.genevan.core;

import com.io7m.jaffirm.core.Invariants;
import com.io7m.junreachable.UnreachableCodeException;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.ResourceBundle;
import java.util.stream.Collectors;

import static com.io7m.genevan.core.GenProtocolErrorCode.AMBIGUOUS_RESULT;
import static com.io7m.genevan.core.GenProtocolErrorCode.CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON;

/**
 * The default protocol solver.
 */

public final class GenProtocolSolver implements GenProtocolSolverType
{
  private final ResourceBundle resources;

  private GenProtocolSolver(
    final ResourceBundle inResources)
  {
    this.resources =
      Objects.requireNonNull(inResources, "resources");
  }

  /**
   * @return The default protocol solver using the system's default locale.
   */

  public static GenProtocolSolverType create()
  {
    return create(Locale.getDefault());
  }

  /**
   * @param locale The locale
   *
   * @return The default protocol solver using the given locale.
   */

  public static GenProtocolSolverType create(
    final Locale locale)
  {
    final var resources =
      ResourceBundle.getBundle(
        "com.io7m.genevan.core.Messages", locale);

    return new GenProtocolSolver(resources);
  }

  /**
   * Find the highest versioned handler that supports the given protocol.
   */

  private static GenProtocolHandlerType bestClientForVersion(
    final Collection<GenProtocolHandlerType> clientSupports,
    final GenProtocolIdentifier protocol)
  {
    return clientSupports.stream()
      .filter(h -> isSupportedByClientHandler(protocol, h))
      .max(Comparator.comparing(o -> o.supported().version()))
      .orElseThrow(UnreachableCodeException::new);
  }

  /**
   * Determine the highest version of each reported server version. It is
   * assumed that all unsupported versions have already been removed with
   * {@link #removeUnsupportedServerVersions(Collection, Collection)}.
   */

  private static Map<String, GenProtocolIdentifier> getHighestVersionsOfEachProtocol(
    final Collection<GenProtocolIdentifier> serverPossible)
  {
    final var distinctProtocols =
      serverPossible.stream()
        .map(GenProtocolIdentifier::identifier)
        .collect(Collectors.toUnmodifiableSet());

    final var protocolsBest =
      new HashMap<String, GenProtocolIdentifier>(distinctProtocols.size());

    for (final var identifier : distinctProtocols) {
      protocolsBest.put(
        identifier,
        serverPossible.stream()
          .filter(p -> Objects.equals(p.identifier(), identifier))
          .max(Comparator.comparing(GenProtocolIdentifier::version))
          .orElseThrow(UnreachableCodeException::new)
      );
    }

    Invariants.checkInvariantV(
      protocolsBest.size() == distinctProtocols.size(),
      "%d == %d",
      Integer.valueOf(protocolsBest.size()),
      Integer.valueOf(distinctProtocols.size())
    );
    return protocolsBest;
  }

  /**
   * Determine if the given protocol is supported by any available client
   * handler.
   */

  private static boolean isSupportedByClientHandlers(
    final GenProtocolIdentifier version,
    final Collection<GenProtocolHandlerType> clientSupports)
  {
    for (final var handler : clientSupports) {
      if (isSupportedByClientHandler(version, handler)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Determine if the given protocol is supported by the given client handler.
   */

  private static boolean isSupportedByClientHandler(
    final GenProtocolIdentifier protocol,
    final GenProtocolHandlerType handler)
  {
    final var c_id = handler.supported();
    if (Objects.equals(protocol.identifier(), c_id.identifier())) {
      final var c_ver = c_id.version();
      final var p_ver = protocol.version();
      return Objects.equals(p_ver.versionMajor(), c_ver.versionMajor());
    }
    return false;
  }

  @Override
  public GenProtocolHandlerType solve(
    final Collection<GenProtocolIdentifier> serverProvides,
    final Collection<GenProtocolHandlerType> clientSupports,
    final List<String> preferProtocols)
    throws GenProtocolException
  {
    Objects.requireNonNull(serverProvides, "serverProvides");
    Objects.requireNonNull(clientSupports, "clientSupports");
    Objects.requireNonNull(preferProtocols, "preferProtocols");

    if (serverProvides.isEmpty()) {
      throw new GenProtocolException(
        CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
        this.format("errorServerSupportsNothing")
      );
    }

    if (clientSupports.isEmpty()) {
      throw new GenProtocolException(
        CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
        this.format("errorClientSupportsNothing")
      );
    }

    final var serverPossible =
      this.removeUnsupportedServerVersions(serverProvides, clientSupports);
    final var protocolsBest =
      getHighestVersionsOfEachProtocol(serverPossible);

    /*
     * If exactly one protocol remains, then a handler can be selected for it.
     */

    if (protocolsBest.size() == 1) {
      return bestClientForVersion(
        clientSupports,
        protocolsBest.values().iterator().next()
      );
    }

    /*
     * Otherwise, if multiple protocols remain, the preferences list will
     * have to be examined in order to resolve the ambiguity.
     */

    for (final var preferred : preferProtocols) {
      final var version = protocolsBest.get(preferred);
      if (version != null) {
        return bestClientForVersion(
          clientSupports,
          version
        );
      }
    }

    throw this.errorAmbiguous(
      protocolsBest.values(),
      clientSupports,
      preferProtocols
    );
  }

  /**
   * First, eliminate any server versions that are not supported by any
   * available client handler.
   */

  private ArrayList<GenProtocolIdentifier> removeUnsupportedServerVersions(
    final Collection<GenProtocolIdentifier> serverProvides,
    final Collection<GenProtocolHandlerType> clientSupports)
    throws GenProtocolException
  {
    final var serverPossible = new ArrayList<>(serverProvides);
    serverPossible.removeIf(v -> {
      return !isSupportedByClientHandlers(v, clientSupports);
    });

    if (serverPossible.isEmpty()) {
      throw this.errorNoProtocolsInCommon(serverProvides, clientSupports);
    }
    return serverPossible;
  }

  private String format(
    final String id,
    final Object... args)
  {
    return MessageFormat.format(this.resources.getString(id), args);
  }

  private GenProtocolException errorNoProtocolsInCommon(
    final Collection<GenProtocolIdentifier> serverProvides,
    final Collection<GenProtocolHandlerType> clientSupports)
  {
    final var lineSeparator = System.lineSeparator();
    final var text = new StringBuilder(128);
    text.append(this.format("errorNoSupportedVersions"));
    text.append(lineSeparator);
    text.append(lineSeparator);

    text.append(this.format("serverSupports"));
    text.append(lineSeparator);

    for (final var candidate : serverProvides) {
      text.append("    ");
      text.append(candidate.identifier());
      text.append(" ");
      text.append(candidate.version().versionMajor());
      text.append(".");
      text.append(candidate.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    text.append(this.format("clientSupports"));
    text.append(lineSeparator);

    for (final var handler : clientSupports) {
      final var supported = handler.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }

    return new GenProtocolException(
      CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
      text.toString()
    );
  }

  private GenProtocolException errorAmbiguous(
    final Collection<GenProtocolIdentifier> serverProvides,
    final Collection<GenProtocolHandlerType> clientSupports,
    final List<String> preferProtocols)
  {
    final var lineSeparator = System.lineSeparator();
    final var text = new StringBuilder(128);
    text.append(this.format("errorAmbiguousProtocols"));
    text.append(lineSeparator);
    text.append(lineSeparator);

    text.append(this.format("serverSupports"));
    text.append(lineSeparator);

    for (final var candidate : serverProvides) {
      text.append("    ");
      text.append(candidate.identifier());
      text.append(" ");
      text.append(candidate.version().versionMajor());
      text.append(".");
      text.append(candidate.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    text.append(this.format("clientSupports"));
    text.append(lineSeparator);

    for (final var handler : clientSupports) {
      final var supported = handler.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    if (!preferProtocols.isEmpty()) {
      text.append(this.format("clientPrefers", preferProtocols));
      text.append(lineSeparator);
    } else {
      text.append(this.format("clientPrefersNone"));
      text.append(lineSeparator);
    }

    text.append(lineSeparator);
    text.append(this.format(
      "clientPreferSuggest",
      serverProvides.stream()
        .map(GenProtocolIdentifier::identifier)
        .toList()
    ));

    return new GenProtocolException(
      AMBIGUOUS_RESULT,
      text.toString()
    );
  }
}
